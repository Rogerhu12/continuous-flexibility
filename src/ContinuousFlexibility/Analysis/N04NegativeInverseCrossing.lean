module

public import ContinuousFlexibility.Analysis.N04NegativeInversePhysicalBounds
public import ContinuousFlexibility.Analysis.N04NegativeInverseScalarComposition
public import ContinuousFlexibility.Analysis.N04NegativeInverseMixedPrefix
public import ContinuousFlexibility.Analysis.PolynomialProductOuterJets
public import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
public import ContinuousFlexibility.Analysis.N06RootJetTransportCalculus
public import ContinuousFlexibility.Analysis.N04NegativeInverseFiniteEnvelope
public import ContinuousFlexibility.Analysis.N04NegativeInversePairSampleEnvelope
public import ContinuousFlexibility.Analysis.N04NegativeInverseCrossingCalculus

/-!
# Actual scalar fields across the old negative cut

The moving inverse point is covered by one of the two closed reference
halves.  On an opposite half the normalized radial coordinate belongs to
a fixed middle band.  The actual chart and height identities then use
fixed smooth scalar transitions on that band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

/-- The same pair of source fields gives either the new radial
coordinate or the new height. -/
def n04NegativeInverseOverlapOuter (height : Bool) (p : ℝ × ℝ) : ℝ :=
  if height then n04NegativeInverseHeightTransition p.1 * p.2
  else n04NegativeInverseRootTransition p.1

/-- The finite source family used by the actual inverse construction. -/
def n04NegativeInverseScalarAtom (i : Fin 3) : Atom :=
  ![Atom.chartRadial, Atom.chartAngleDefect, Atom.height] i

theorem n04NegativeInverseScalarAtom_physical (i : Fin 3) :
    negativePhysicalGeometryAtom (n04NegativeInverseScalarAtom i) := by
  fin_cases i <;> trivial

theorem n04NegativeInverseScalarAtom_property
    {P : Atom → Prop} (hr : P .chartRadial) (ha : P .chartAngleDefect)
    (hh : P .height) (i : Fin 3) : P (n04NegativeInverseScalarAtom i) := by
  fin_cases i
  · exact hr
  · exact ha
  · exact hh

theorem n04NegativeInverseScalarAtom_jet_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : Atom → E → ℝ} {n : ℕ} {x : E} {v : Fin n → E} {bound : ℝ}
    (hr : ∀ Q : SmoothDirections U (f .chartRadial), ‖Q.D n x v‖ ≤ bound)
    (ha : ∀ Q : SmoothDirections U (f .chartAngleDefect), ‖Q.D n x v‖ ≤ bound)
    (hh : ∀ Q : SmoothDirections U (f .height), ‖Q.D n x v‖ ≤ bound)
    (i : Fin 3) (Q : SmoothDirections U (f (n04NegativeInverseScalarAtom i))) :
    ‖Q.D n x v‖ ≤ bound :=
  n04NegativeInverseScalarAtom_property
    (P := fun a => ∀ J : SmoothDirections U (f a), ‖J.D n x v‖ ≤ bound) hr ha hh i Q

private theorem n04NegativeInverse_nil_prefix
    {x M H t : ℝ} {shift : ℕ}
    (h : x ≤ M * parameterHeightWeight H StateAngleWord.nil.stateArity *
      t ^ (StateAngleWord.nil.angleArity + shift * StateAngleWord.nil.stateArity - 1)) :
    x ≤ M := by
  simpa only [StateAngleWord.stateArity, StateAngleWord.angleArity,
    Nat.mul_zero, Nat.add_zero, Nat.zero_sub, parameterHeightWeight, if_true,
    pow_zero, mul_one] using h

theorem n04NegativeInverseOverlapOuter_contDiffOn (height : Bool) :
    ContDiffOn ℝ ∞ (n04NegativeInverseOverlapOuter height)
      (Ioo (1 / 2 : ℝ) (4 / 3) ×ˢ (univ : Set ℝ)) := by
  cases height
  · exact n04NegativeInverseRootTransition_contDiffOn.comp contDiff_fst.contDiffOn
      (fun p hp => hp.1)
  · exact (n04NegativeInverseHeightTransition_contDiffOn.comp contDiff_fst.contDiffOn
      (fun p hp => hp.1)).mul contDiff_snd.contDiffOn

private theorem n04NegativeInverse_middle_finiteJets
    {f : ℝ → ℝ} (hf : ∀ x ∈ Ioo (1 / 2 : ℝ) (4 / 3), ContDiffAt ℝ ∞ f x)
    (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n ≤ N, ∀ x ∈ Icc (3 / 4 : ℝ) (5 / 4),
      ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  classical
  choose c hc hb using fun n : Fin (N + 1) =>
    n04NegativeInverse_middle_iteratedDeriv_bound hf n.val
  let C := 1 + ∑ n : Fin (N + 1), c n
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun n _ => (hc n).le))
  refine ⟨C, hC, ?_⟩
  intro n hn x hx
  have hcn : c ⟨n, by omega⟩ ≤ C :=
    (Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ _)).trans
      (le_add_of_nonneg_left zero_le_one)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (hb ⟨n, by omega⟩ x hx).trans hcn

/-- All outer derivatives have only a linear cost in the source height.
The first coordinate lies in one fixed compact interval. -/
theorem n04NegativeInverseOverlapOuter_finiteJets (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ height : Bool, ∀ n ≤ N, ∀ p : ℝ × ℝ,
      p.1 ∈ Icc (3 / 4 : ℝ) (5 / 4) →
      ‖iteratedFDeriv ℝ n (n04NegativeInverseOverlapOuter height) p‖ ≤
        (2 : ℝ) ^ N * C * (1 + |p.2|) := by
  obtain ⟨CR, hCR, hroot⟩ := n04NegativeInverse_middle_finiteJets
    (fun _ hx => n04NegativeInverseRootTransition_contDiffAt hx) N
  obtain ⟨CH, hCH, hheight⟩ := n04NegativeInverse_middle_finiteJets
    (fun _ hx => n04NegativeInverseHeightTransition_contDiffAt hx) N
  let C := max CR CH
  have hC : 1 ≤ C := hCR.trans (le_max_left _ _)
  let fst : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let snd : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfst : ‖fst‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound fst zero_le_one
    (fun p => by
      simpa only [fst, ContinuousLinearMap.coe_fst', one_mul] using norm_fst_le p)
  have hsnd : ‖snd‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound snd zero_le_one
    (fun p => by
      simpa only [snd, ContinuousLinearMap.coe_snd', one_mul] using norm_snd_le p)
  refine ⟨C, hC, ?_⟩
  intro height n hn p hp
  have hpopen : p.1 ∈ Ioo (1 / 2 : ℝ) (4 / 3) :=
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hscalar {f : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f p.1)
      (hbound : ∀ j ≤ N, ‖iteratedFDeriv ℝ j f p.1‖ ≤ C) (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => f q.1) p‖ ≤ C := by
    have h := norm_iteratedFDeriv_comp_linear_le_at fst hf j
    have hpow : ‖fst‖ ^ j ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg fst) hfst j
    exact h.trans ((mul_le_mul (hbound j hj) hpow (pow_nonneg (norm_nonneg _) _)
      (zero_le_one.trans hC)).trans_eq (mul_one C))
  have hroot' := hscalar (n04NegativeInverseRootTransition_contDiffAt hpopen)
    (fun j hj => (hroot j hj p.1 hp).trans (le_max_left _ _))
  have hheight' := hscalar (n04NegativeInverseHeightTransition_contDiffAt hpopen)
    (fun j hj => (hheight j hj p.1 hp).trans (le_max_right _ _))
  have hsnd' (j : ℕ) : ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => q.2) p‖ ≤ 1 + |p.2| := by
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        (le_add_of_nonneg_left zero_le_one : |p.2| ≤ 1 + |p.2|)
    | succ j =>
        simpa only [snd, ContinuousLinearMap.coe_snd'] using
          (norm_iteratedFDeriv_linear_of_pos snd (j + 1) (by omega) p).trans
            (hsnd.trans (le_add_of_nonneg_right (abs_nonneg _)))
  cases height with
  | false =>
      apply (hroot' n hn).trans
      have htwo : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
      have hvalue : 1 ≤ 1 + |p.2| := le_add_of_nonneg_right (abs_nonneg _)
      exact (le_mul_of_one_le_left (zero_le_one.trans hC) htwo).trans
        (le_mul_of_one_le_right
          (mul_nonneg (pow_nonneg (by norm_num) _) (zero_le_one.trans hC)) hvalue)
  | true =>
      have hprod := n06_norm_iteratedFDeriv_mul_at_le
        ((n04NegativeInverseHeightTransition_contDiffAt hpopen).comp p contDiffAt_fst)
        contDiffAt_snd n (zero_le_one.trans hC)
        (add_nonneg zero_le_one (abs_nonneg _))
        (fun j hj => hheight' j (hj.trans hn)) (fun j _ => hsnd' j)
      exact hprod.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn)
          (zero_le_one.trans hC)) (add_nonneg zero_le_one (abs_nonneg _)))

/-- The fixed outer transition can be applied on the open preimage of
its middle interval.  Both compared towers remain the genuine towers
of the same original functions. -/
theorem n04NegativeInverse_overlapScalar_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ × ℝ} {g : E → ℝ}
    (J : SmoothDirections U f) (Q : SmoothDirections U g) (height : Bool)
    (heq : ∀ x ∈ U, g x = n04NegativeInverseOverlapOuter height (f x))
    {x : E} (hx : x ∈ U) (hband : (f x).1 ∈ Icc (3 / 4 : ℝ) (5 / 4))
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) (w : StateAngleWord n)
    (shift : ℕ) (hshift : 1 ≤ shift)
    {C M H L t : ℝ} (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (houter : ∀ height : Bool, ∀ j ≤ N, ∀ p : ℝ × ℝ,
      p.1 ∈ Icc (3 / 4 : ℝ) (5 / 4) →
      ‖iteratedFDeriv ℝ j (n04NegativeInverseOverlapOuter height) p‖ ≤
        (2 : ℝ) ^ N * C * (1 + |p.2|))
    (hvalue : |(f x).2| ≤ M)
    (v : Fin n → E)
    (hinner : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ ≤
        M * parameterHeightWeight H (w.restrict (c.emb i)).stateArity *
          t ^ ((w.restrict (c.emb i)).angleArity +
            shift * (w.restrict (c.emb i)).stateArity - 1)) :
    ‖Q.D n x v‖ ≤
      ((2 : ℝ) ^ N * C * (1 + M)) * (Fintype.card (OrderedFinpartition n) : ℝ) *
        (M * L) ^ n * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) := by
  let V := Ioo (1 / 2 : ℝ) (4 / 3) ×ˢ (univ : Set ℝ)
  let U' := U ∩ f ⁻¹' V
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_univ
  have hU' : IsOpen U' := J.continuousOn.isOpen_inter_preimage J.open_domain hV
  have hx' : x ∈ U' := ⟨hx,
    ⟨⟨by linarith [hband.1], by linarith [hband.2]⟩, mem_univ _⟩⟩
  let J' : SmoothDirections U' f := J.restrict hU' inter_subset_left
  let Q' : SmoothDirections U' (n04NegativeInverseOverlapOuter height ∘ f) :=
    (Q.restrict hU' inter_subset_left).congrOn (fun y hy => heq y hy.1)
  have hout (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (n04NegativeInverseOverlapOuter height) (f x)‖ ≤
        (2 : ℝ) ^ N * C * (1 + M) :=
    (houter height j (hj.trans hnN) (f x) hband).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hvalue)
        (mul_nonneg (pow_nonneg (by norm_num) _) (zero_le_one.trans hC)))
  exact n04NegativeInverse_contDiff_comp_sharp_bound
    (X := E) (Y := ℝ × ℝ) (Z := ℝ) (U := U') (V := V)
    (f := f) (g := n04NegativeInverseOverlapOuter height) J' Q' hV
    (n04NegativeInverseOverlapOuter_contDiffOn height) (fun y hy => hy.2)
    hn w shift hshift hx'
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (zero_le_one.trans hC))
      (by linarith : 0 ≤ 1 + M)) hM hH hHL hL ht hout v hinner

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Restrict the actual whole-component field tower to a chosen
admissible parameter neighborhood. -/
def negativeInverse_componentAtomJointTowerOn
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    (a : Atom) (ha : negativePhysicalGeometryAtom a) :
    SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ
      (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
      (fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily 0 a x.1 k x.2) :=
  (G.negativeInverse_componentAtomJointTower 0 k m side hi a ha).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1
      hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)

theorem negativeInverse_atom_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) (k : ℕ) :
    G.atomFamily η a 0 k = G.atomRef η a k := by
  have hlift : G.lift η (0 : Parameter G.W.S) = G.ref η :=
    (liftSectorParameter_eq_affine (G.S η) (G.C η) 0).trans
      ((congrArg (fun w : AnnularState (G.S η) × ℝ => ((G.C η).referenceState, 0) + w)
        (ContinuousLinearMap.map_zero (sectorParameterInclusion (G.S η)))).trans (add_zero _))
  exact congrArg (fun z => atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z k a) hlift

/-- These are the literal normalized radial, angular-defect and height
fields, on the whole physical plane where their values are defined. -/
theorem negativeInverse_physicalAtom_fields
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) (p : PolarPoint) :
    G.negativeInversePhysicalAtomFamily η .chartRadial z k p =
        (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side p).1 /
          n04bRootCutRadius (G.W.C.travel m) ∧
      G.negativeInversePhysicalAtomFamily η .chartAngleDefect z k p =
        (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side p).2 - p.2 ∧
      G.negativeInversePhysicalAtomFamily η .height z k p =
        n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side p := by
  have hf := G.negativeInverse_actual_fields η z k m side hi
  have lengthData := G.negativeInverse_length_values
  have hlength := lengthData.choose_spec.2
  have hp : physicalUnitPoint (G.V η) k
      (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p) = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η))
      (sub_pos.mp (hlength η k).1) p
  have hchart : (G.V η).chart (G.lift η z) k
      (physicalUnitPoint (G.V η) k
        (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p)) =
      n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) m side p :=
    congrArg₂ (fun (F : PolarPoint → PolarPoint) (q : PolarPoint) => F q)
      hf.2.2.2.2.1 hp
  have hheight : (G.V η).height (G.lift η z) k
      (physicalUnitPoint (G.V η) k
        (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p)) =
      n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) m side p :=
    congrArg₂ (fun (H : PolarPoint → ℝ) (q : PolarPoint) => H q)
      hf.2.2.2.2.2.2 hp
  have hbounds : ((G.V η).left k, (G.V η).right k) =
      ((0 : ℝ), n04bRootCutRadius (G.W.C.travel m)) :=
    Prod.ext hf.1 hf.2.1
  refine ⟨?_, ?_, ?_⟩
  · change (((G.V η).chart (G.lift η z) k
      (physicalUnitPoint (G.V η) k
        (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p))).1 -
        (G.V η).left k) / ((G.V η).right k - (G.V η).left k) = _
    simpa only [sub_zero] using
      (congrArg₂ (fun (q : PolarPoint) (bounds : PolarPoint) =>
        (q.1 - bounds.1) / (bounds.2 - bounds.1)) hchart hbounds)
  · change ((G.V η).chart (G.lift η z) k
      (physicalUnitPoint (G.V η) k
        (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p))).2 - p.2 = _
    exact congrArg (fun q : PolarPoint => q.2 - p.2) hchart
  · change (G.V η).height (G.lift η z) k
      (physicalUnitPoint (G.V η) k
        (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p)) = _
    exact hheight

theorem negativeInverse_referenceRadial_le_one
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    {p : PolarPoint}
    (hp : p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))
    (hhalf : p ∈ Icc ((G.V η).physicalLeft k) ((G.V η).physicalRight k) ×ˢ
      (univ : Set ℝ)) :
    G.negativeInversePhysicalAtomFamily η .chartRadial 0 k p ≤ 1 := by
  let J := G.negativeInverse_componentAtomJointTower η k m side hi .chartRadial trivial
  have hzero : (0 : Parameter G.W.S) ∈
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε := by
    constructor
    · change sectorGrading G.W.S G.W.base 0 < G.W.ε
      exact (sectorGrading G.W.S G.W.base).map_zero'.trans_lt G.W.ε_pos
    · change |(0 : ℝ)| < G.W.ε
      simpa only [abs_zero] using G.W.ε_pos
  have lengthData := G.negativeInverse_length_values
  have hl := lengthData.choose_spec.2
  have hlen : (G.V η).physicalLeft k < (G.V η).physicalRight k :=
    sub_pos.mp (hl η k).1
  apply n04NegativeInverse_le_on_closedHalf hlen hhalf
  · exact n04NegativeInverse_fixedParameter_continuousAt
      (E := Parameter G.W.S)
      (U := sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
      (Ω := Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))
      (f := fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily η .chartRadial x.1 k x.2) J hzero hp
  · intro r hr
    let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k r
    have hpq : physicalUnitPoint (G.V η) k q = r :=
      n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η)) hlen r
    change G.atomFamily η .chartRadial 0 k q ≤ 1
    refine ((congrFun (G.negativeInverse_atom_zero η .chartRadial k) q).trans
      (congrFun (G.negative_atomRef η k (m, side) hi .chartRadial (by decide)) q)).trans_le ?_
    let K := G.W.A G.X.e₀
    let j := G.negativeIndex (m, side)
    have hf := G.negative_fields η (G.W.C.referenceState, 0) k (m, side) hi
    have hleft : (G.V η).physicalLeft k = K.physicalLeft j := hf.2.2.1
    have hright : (G.V η).physicalRight k = K.physicalRight j := hf.2.2.2.1
    have hphysicalEq : physicalUnitPoint (G.V η) k q = physicalUnitPoint K j q :=
      congrArg₂ (fun a b : ℝ => (a + (b - a) * q.1, q.2)) hleft hright
    have hphysical : physicalUnitPoint K j q = r := hphysicalEq.symm.trans hpq
    have hreference : r ∈ referencePhysicalPieceOpen G.W.S K j := by
      change r ∈ Ioo (K.physicalLeft j) (K.physicalRight j) ×ˢ (univ : Set ℝ)
      exact ⟨⟨hleft.symm.trans_lt hr.1.1, hr.1.2.trans_eq hright⟩, mem_univ _⟩
    have hA := n04b_actualTypedAtlas_partA G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
    have hdomain : physicalPieceOpen G.W.S K (G.W.C.referenceState, 0) j =
        referencePhysicalPieceOpen G.W.S K j := hA.referenceDomain j
    have hcurrent : r ∈ physicalPieceOpen G.W.S K (G.W.C.referenceState, 0) j :=
      hdomain.symm ▸ hreference
    have hmap := (hA.charts (G.W.C.referenceState, 0)
      (reference_mem_stateNeighborhood G.W.S G.W.C G.W.base G.W.ε_pos)
      G.W.through03.1.1.2.2.1.stateSector j).1 hcurrent
    change ((K.chart (G.W.C.referenceState, 0) j (physicalUnitPoint K j q)).1 - K.left j) /
      (K.right j - K.left j) ≤ 1
    exact (congrArg (fun p : PolarPoint =>
      ((K.chart (G.W.C.referenceState, 0) j p).1 - K.left j) /
        (K.right j - K.left j)) hphysical).trans_le
          ((div_le_one (sub_pos.mpr (hA.referenceBounds j).2.1)).mpr
            (sub_le_sub_right hmap.1.2.le _))

/-- A single parameter neighborhood controls the normalized radial
difference on both closed reference halves, including their shared cut. -/
theorem negativeInverse_radial_closedHalf_small
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (h : G.Data 0 (G.Neg 0) b ε (G.atomFamily 0 .chartRadial) (G.atomRef 0 .chartRadial)) :
    ∃ b' : ℕ, ∃ ε' : ℝ, b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood G.W.S b' ε' ε', ∀ k m side,
        G.e k = .inl (m, side) →
      ∀ p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ),
        p ∈ Icc ((G.V 0).physicalLeft k) ((G.V 0).physicalRight k) ×ˢ (univ : Set ℝ) →
        |G.negativeInversePhysicalAtomFamily 0 .chartRadial z k p -
          G.negativeInversePhysicalAtomFamily 0 .chartRadial 0 k p| ≤ 1 / 4 := by
  have hbound :=
    G.negativeInverse_atomData_uniform_small hadm.2.1 .chartRadial (by decide) h 0 0
      (by norm_num : (0 : ℝ) < 1 / 4)
  let b' : ℕ := hbound.choose
  let ε' : ℝ := hbound.choose_spec.choose
  have hb : b ≤ b' := hbound.choose_spec.choose_spec.1
  have hε' : 0 < ε' := hbound.choose_spec.choose_spec.2.1
  have hε'ε : ε' ≤ ε := hbound.choose_spec.choose_spec.2.2.1
  have hsmall := hbound.choose_spec.choose_spec.2.2.2
  have lengthData := G.negativeInverse_length_values
  have hl := lengthData.choose_spec.2
  refine ⟨b', ε', hb, hε', hε'ε, ?_⟩
  intro z hz k m side hi p hp hhalf
  have hzfull := sectorNeighborhood_mono G.W.S (hadm.1.trans hb)
    (hε'ε.trans hadm.2.2.1) (hε'ε.trans hadm.2.2.1) hz
  have hzero : (0 : Parameter G.W.S) ∈
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε := by
    constructor
    · change sectorGrading G.W.S G.W.base 0 < G.W.ε
      exact (sectorGrading G.W.S G.W.base).map_zero'.trans_lt G.W.ε_pos
    · change |(0 : ℝ)| < G.W.ε
      simpa only [abs_zero] using G.W.ε_pos
  let J := G.negativeInverse_componentAtomJointTower 0 k m side hi .chartRadial trivial
  have hlen : (G.V 0).physicalLeft k < (G.V 0).physicalRight k := sub_pos.mp (hl 0 k).1
  apply n04NegativeInverse_le_on_closedHalf hlen hhalf
  · have hcurrent : ContinuousAt
        (fun p : PolarPoint => G.negativeInversePhysicalAtomFamily 0 .chartRadial z k p) p :=
      n04NegativeInverse_fixedParameter_continuousAt
        (E := Parameter G.W.S)
        (U := sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
        (Ω := Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))
        (f := fun x : Parameter G.W.S × PolarPoint =>
          G.negativeInversePhysicalAtomFamily 0 .chartRadial x.1 k x.2) J hzfull hp
    have href : ContinuousAt
        (fun p : PolarPoint => G.negativeInversePhysicalAtomFamily 0 .chartRadial 0 k p) p :=
      n04NegativeInverse_fixedParameter_continuousAt
        (E := Parameter G.W.S)
        (U := sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
        (Ω := Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))
        (f := fun x : Parameter G.W.S × PolarPoint =>
          G.negativeInversePhysicalAtomFamily 0 .chartRadial x.1 k x.2) J hzero hp
    exact (hcurrent.sub href).abs
  · intro r hr
    let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V 0)) k r
    have hq : q ∈ unitStrip :=
      n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData (G.V 0)) hlen hr
    have hk : G.Neg 0 k := (G.neg_iff_inl 0 k).mpr ⟨(m, side), hi⟩
    have hs := hsmall 0 z hz k hk ⟨q, hq⟩ 0 0 (by omega)
    have hs0 : |G.atomFamily 0 .chartRadial z k q - G.atomRef 0 .chartRadial k q| <
        1 / 4 := n04NegativeInverse_mixedZero_lt
      (f := G.atomFamily 0 .chartRadial z k) (g := G.atomRef 0 .chartRadial k)
      (q := q) hs
    change |G.atomFamily 0 .chartRadial z k q - G.atomFamily 0 .chartRadial 0 k q| ≤ 1 / 4
    exact (congrArg (fun t : ℝ => |G.atomFamily 0 .chartRadial z k q - t|)
      (congrFun (G.negativeInverse_atom_zero 0 .chartRadial k) q)).trans_le hs0.le

/-- The three scalar fields obey the actual opposite-half identities
throughout their original component. -/
theorem negativeInverse_physicalAtom_opposite
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter G.W.S} (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (k k' m : ℕ) (side : Bool)
    (hi : G.e k = .inl (m, side)) (hi' : G.e k' = .inl (m, !side))
    {p : PolarPoint}
    (hp : p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)) :
    G.negativeInversePhysicalAtomFamily η .chartRadial z k p =
        n04NegativeInverseRootTransition
          (G.negativeInversePhysicalAtomFamily η .chartRadial z k' p) ∧
      G.negativeInversePhysicalAtomFamily η .chartAngleDefect z k p =
        G.negativeInversePhysicalAtomFamily η .chartAngleDefect z k' p ∧
      G.negativeInversePhysicalAtomFamily η .height z k p =
        n04NegativeInverseHeightTransition
            (G.negativeInversePhysicalAtomFamily η .chartRadial z k' p) *
          G.negativeInversePhysicalAtomFamily η .height z k' p := by
  have hf := G.negativeInverse_physicalAtom_fields η z k m side hi p
  have hf' := G.negativeInverse_physicalAtom_fields η z k' m (!side) hi' p
  rw [hf.1, hf.2.1, hf.2.2, hf'.1, hf'.2.1, hf'.2.2]
  refine ⟨G.W.negativeChart_normalizedRoot_transition m side hz hp, ?_,
    G.W.negativeHeight_opposite_transition m side hz hp⟩
  exact congrArg (fun r : ℝ => r - p.2) (G.W.negativeChart_opposite_angular_eq m side hz hp)

/-- When the inverse target lies in one current half and its preimage
belongs to the opposite old half, the latter radial argument lies in a
fixed compact interval of the transition domain. -/
theorem negativeInverse_opposite_middleBand
    {z : Parameter G.W.S} (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (k k' m : ℕ) (side : Bool)
    (hi : G.e k = .inl (m, side)) (hi' : G.e k' = .inl (m, !side))
    {p : PolarPoint}
    (hp : p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))
    (hhalf : p ∈ Icc ((G.V 0).physicalLeft k') ((G.V 0).physicalRight k') ×ˢ
      (univ : Set ℝ))
    (htarget : G.negativeInversePhysicalAtomFamily 0 .chartRadial z k p ∈ Ioo (0 : ℝ) 1)
    (hclose : |G.negativeInversePhysicalAtomFamily 0 .chartRadial z k' p -
      G.negativeInversePhysicalAtomFamily 0 .chartRadial 0 k' p| ≤ 1 / 4) :
    G.negativeInversePhysicalAtomFamily 0 .chartRadial z k' p ∈
      Icc (3 / 4 : ℝ) (5 / 4) := by
  have hf := G.negativeInverse_physicalAtom_fields 0 z k m side hi p
  have hf' := G.negativeInverse_physicalAtom_fields 0 z k' m (!side) hi' p
  have hw := liftSectorParameter_mem_stateNeighborhood (C := G.W.C) hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hT := n04b_actualTravel_positive G.W.through03 G.W.hS G.W.hT G.W.field hw hs m
  have hy : 0 ≤ G.negativeInversePhysicalAtomFamily 0 .chartRadial z k' p := by
    rw [hf'.1, ((n04bActualNegativeFunctions_spec G.W.hT G.W.hS G.W.through03 G.W.field
      hw hs m (!side)).component_chart_germ hp).self_of_nhds]
    exact div_nonneg (G.W.negativeRootChart_radial_pos m (!side) hz hp).le
      (n04bRootCutRadius_pos hT).le
  have hsum :
      G.negativeInversePhysicalAtomFamily 0 .chartRadial z k p ^ (3 / 2 : ℝ) +
        G.negativeInversePhysicalAtomFamily 0 .chartRadial z k' p ^ (3 / 2 : ℝ) = 2 := by
    rw [hf.1, hf'.1]
    exact G.W.negativeChart_normalizedRoot_power_sum m side hz hp
  have hb := n04NegativeInverse_normalized_coordinates_band htarget hy hsum
    (G.negativeInverse_referenceRadial_le_one 0 k' m (!side) hi' hp hhalf) hclose
  exact ⟨(by norm_num : (3 / 4 : ℝ) ≤ 1).trans hb.2.1.1, hb.2.1.2⟩

/-- On one fixed small neighborhood, all three actual scalar inputs
have sharp pure prefixes at every point of the current target half.
The point may lie on either side of the old cut.  The returned base
precedes the parameter prefix, and its radius is at most one half. -/
theorem negativeInverse_componentScalars_purePrefix
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (hc : G.NegativeAtomData 0 atomIsNegativeChart b ε)
    (hh : G.NegativeAtomData 0 atomIsNegativeHeight b ε) :
    ∃ low : ℕ, ∃ ε' : ℝ, b ≤ low ∧ G.Admissible low ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ a : Fin 3, ∀ k m side (hi : G.e k = .inl (m, side)),
        ∀ J : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
          (fun x : Parameter G.W.S × PolarPoint =>
            G.negativeInversePhysicalAtomFamily 0 (n04NegativeInverseScalarAtom a) x.1 k x.2),
        ∀ z ∈ sectorNeighborhood G.W.S low ε' ε',
        ∀ p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ),
          G.negativeInversePhysicalAtomFamily 0 .chartRadial z k p ∈ Ioo (0 : ℝ) 1 →
        ∀ n : ℕ, 0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K → w.angleArity ≤ s →
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
  have hdata (a : Fin 3) : G.Data 0 (G.Neg 0) b ε
      (G.atomFamily 0 (n04NegativeInverseScalarAtom a))
      (G.atomRef 0 (n04NegativeInverseScalarAtom a)) :=
    n04NegativeInverseScalarAtom_property
      (P := fun atom => G.Data 0 (G.Neg 0) b ε (G.atomFamily 0 atom) (G.atomRef 0 atom))
      (hc .chartRadial trivial) (hc .chartAngleDefect trivial) (hh .height trivial) a
  have hfamily := G.negativeInverse_physicalFamily_purePrefix
    hadm n04NegativeInverseScalarAtom n04NegativeInverseScalarAtom_physical hdata
  let base : ℕ := hfamily.choose
  have hbase : b ≤ base := hfamily.choose_spec.1
  have hprefix := hfamily.choose_spec.2
  have hbound :=
    G.negativeInverse_radial_closedHalf_small hadm (hc .chartRadial trivial)
  let smallBase : ℕ := hbound.choose
  let radius : ℝ := hbound.choose_spec.choose
  have hsmallBase : b ≤ smallBase := hbound.choose_spec.choose_spec.1
  have hradius : 0 < radius := hbound.choose_spec.choose_spec.2.1
  have hradiusε : radius ≤ ε := hbound.choose_spec.choose_spec.2.2.1
  have hsmall := hbound.choose_spec.choose_spec.2.2.2
  let low := max base smallBase
  let ε' := min radius (1 / 2)
  have hlow : b ≤ low := hbase.trans (le_max_left _ _)
  have hε' : 0 < ε' := lt_min hradius (by norm_num)
  have hε'ε : ε' ≤ ε := (min_le_left _ _).trans hradiusε
  have hε'half : ε' ≤ 1 / 2 := min_le_right _ _
  have hadm' : G.Admissible low ε' := G.admissible_mono hadm hlow hε' hε'ε
  have hU := isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have heightData := material_sample_height_coefficient_power_bounded
    G.W.radial.1 hU (G.V 0).cell 0 (by norm_num : (0 : ℝ) < 3 / 4)
  let CH : ℝ := heightData.choose
  have hheight := heightData.choose_spec.2
  let L := max 1 CH
  have hL : 1 ≤ L := le_max_left _ _
  have hheightL (k : ℕ) :
      G.W.U.H (G.W.U.sample ((G.V 0).cell k)) ^ (3 / 4 : ℝ) ≤ L :=
    (n04NegativeInverse_remove_rpow_zero (C := CH) (hheight k)).trans (le_max_right _ _)
  have hmono : Monotone (parameterGrading G.W.S) := sectorPairGrading_monotone G.W.S
  refine ⟨low, ε', hlow, hadm', hε'ε, hε'half, fun K => ?_⟩
  let shift : ℕ := (hprefix K).choose
  have hshift : 1 ≤ shift := (hprefix K).choose_spec.1
  have hpref := (hprefix K).choose_spec.2
  refine ⟨shift, hshift, fun s => ?_⟩
  let C : ℝ := (hpref s).choose
  have hC : 0 < C := (hpref s).choose_spec.1
  have hb := (hpref s).choose_spec.2
  have transferData := G.negativeInverse_pair_sample_heightWeight C hC.le
  let D : ℝ := transferData.choose
  have hD : 1 ≤ D := transferData.choose_spec.1
  have htransfer := transferData.choose_spec.2
  have outerData := n04NegativeInverseOverlapOuter_finiteJets (s + K)
  let CO : ℝ := outerData.choose
  have hCO : 1 ≤ CO := outerData.choose_spec.1
  have houter := outerData.choose_spec.2
  have packedData := n04NegativeInverse_finiteComposition_envelope (s + K) hCO hL hD
  let B : ℝ := packedData.choose
  have hB : 1 ≤ B := packedData.choose_spec.1
  have hpack := packedData.choose_spec.2
  refine ⟨B, zero_lt_one.trans_le hB, ?_⟩
  intro a k m side hi J z hz p hp htarget n hn w hwK hws v hvlow R hR hzR hvR hvphys hvstate hvspatial
  have hzold : z ∈ sectorNeighborhood G.W.S b ε ε :=
    sectorNeighborhood_mono G.W.S hlow hε'ε hε'ε hz
  have hzfull : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono G.W.S hadm'.1 hadm'.2.2.1 hadm'.2.2.1 hz
  have hzbase : parameterGrading G.W.S base z ≤ 1 := by
    have ht := n07a_parameterGrading_lt_twice_radius (le_max_left base smallBase) hz
    exact ht.le.trans (by nlinarith only [hε'half])
  have hbaselow : base ≤ low := le_max_left _ _
  have hhigh : base + s + shift * K + 1 ≤ low + s + shift * K + 1 := by omega
  have hzRold : parameterGrading G.W.S (base + s + shift * K + 1) z ≤ R :=
    (hmono hhigh z).trans hzR
  let E := G.W.U.E0 (G.W.U.sample ((G.V 0).cell k))
  let H := G.W.U.H (G.W.U.sample ((G.V 0).cell k)) ^ (3 / 4 : ℝ)
  let M := D * E ^ D
  let t : ℝ := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 k
  have hM : 1 ≤ M := n04NegativeInverse_envelope_one_le hD hE
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 k) _
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hpower (d : ℕ) : t ^ d = R ^ ((d : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) :=
    n04NegativeInverse_commonScale_pow (zero_le_one.trans hR) d (s + shift * K)
  have coverData := G.negativeInverse_referenceHalf_cover 0 m hp
  let source : Bool := coverData.choose
  have hhalf := coverData.choose_spec
  let k' := G.e.symm (.inl (m, source))
  have hi' : G.e k' = .inl (m, source) := G.e.apply_symm_apply _
  have sourceBound (a' : Fin 3)
      (Q : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
        (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
        (fun x : Parameter G.W.S × PolarPoint =>
          G.negativeInversePhysicalAtomFamily 0 (n04NegativeInverseScalarAtom a') x.1 k' x.2))
      (j : ℕ) (word : StateAngleWord j) (hwordK : word.stateArity ≤ K)
      (hwords : word.angleArity ≤ s) (u : Fin j → Parameter G.W.S × PolarPoint)
      (hulow : ∀ i, parameterGrading G.W.S low (u i).1 ≤ 1)
      (huhigh : ∀ i, parameterGrading G.W.S (low + s + shift * K + 1) (u i).1 ≤ R)
      (huphys : ∀ i, ‖(u i).2‖ ≤ 1)
      (hustate : ∀ i, word.isState i = false → (u i).1 = 0)
      (huspatial : ∀ i, word.isState i = true → (u i).2 = 0) :
      ‖Q.D j (z, p) u‖ ≤ M * parameterHeightWeight H word.stateArity *
        t ^ (word.angleArity + shift * word.stateArity - 1) := by
    let Qold := G.negativeInverse_componentAtomJointTowerOn hadm k' m source hi'
      (n04NegativeInverseScalarAtom a') (n04NegativeInverseScalarAtom_physical a')
    let Qnew := Qold.restrict
      ((sectorNeighborhood_isOpen G.W.S low ε' ε').prod (isOpen_Ioo.prod isOpen_univ))
      (fun x hx => ⟨sectorNeighborhood_mono G.W.S hlow hε'ε hε'ε hx.1, hx.2⟩)
    have he : Q.D j (z, p) u = Qold.D j (z, p) u :=
      congrArg (fun A : (Parameter G.W.S × PolarPoint) [×j]→L[ℝ] ℝ => A u)
        (Q.unique Qnew j (z, p) ⟨hz, hp⟩)
    let Es := G.W.U.E0 (G.W.U.sample ((G.V 0).cell k'))
    let Hs := G.W.U.H (G.W.U.sample ((G.V 0).cell k')) ^ (3 / 4 : ℝ)
    have hraw : ‖Qold.D j (z, p) u‖ ≤ C * Es ^ C *
        parameterHeightWeight Hs word.stateArity *
          R ^ (((word.angleArity + shift * word.stateArity - 1 : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) :=
      hb a' k' m source hi' Qold z hzold hzbase p hp hhalf j word
        hwordK hwords u (fun i => (hmono hbaselow (u i).1).trans (hulow i)) R hR hzRold
        (fun i => (hmono hhigh (u i).1).trans (huhigh i)) huphys hustate huspatial
    have hcost : C * Es ^ C * parameterHeightWeight Hs word.stateArity ≤
        M * parameterHeightWeight H word.stateArity :=
      htransfer 0 k k' m side source hi hi' word.stateArity
    have hscaled : ‖Qold.D j (z, p) u‖ ≤ M * parameterHeightWeight H word.stateArity *
        R ^ (((word.angleArity + shift * word.stateArity - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) :=
      hraw.trans (mul_le_mul_of_nonneg_right hcost
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
    exact ((congrArg norm he).trans_le hscaled).trans_eq
      (congrArg (fun r : ℝ => M * parameterHeightWeight H word.stateArity * r)
        (hpower (word.angleArity + shift * word.stateArity - 1))).symm
  have hfinish {x : ℝ} (hx : x ≤ M * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1)) :
      x ≤ B * E ^ B * parameterHeightWeight H w.stateArity *
        R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) := by
    have hcost : M ≤ B * E ^ B := (hpack E hE).1
    have hscaled := n04NegativeInverse_prefix_mono hcost
      (parameterHeightWeight_nonneg hH w.stateArity)
      (pow_nonneg (zero_le_one.trans ht) (w.angleArity + shift * w.stateArity - 1)) hx
    exact hscaled.trans_eq
      (congrArg (fun r : ℝ => B * E ^ B * parameterHeightWeight H w.stateArity * r)
        (hpower (w.angleArity + shift * w.stateArity - 1)))
  by_cases hsame : source = side
  · have hkk : k' = k := G.e.injective (by
      calc
        G.e k' = .inl (m, source) := hi'
        _ = .inl (m, side) := by rw [hsame]
        _ = G.e k := hi.symm)
    let Q : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
        (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
        (fun x : Parameter G.W.S × PolarPoint =>
          G.negativeInversePhysicalAtomFamily 0 (n04NegativeInverseScalarAtom a) x.1 k' x.2) :=
      J.congrOn (fun x hx => by rw [hkk])
    exact hfinish (sourceBound a Q n w hwK hws v hvlow hvR hvphys hvstate hvspatial)
  · have hopposite : source = !side := by
      have hbool : source = side ∨ source = !side := by cases source <;> cases side <;> simp
      exact hbool.resolve_left hsame
    have hiOpp : G.e k' = .inl (m, !side) :=
      hi'.trans (congrArg (fun b : Bool => Sum.inl (m, b)) hopposite)
    have hzsmall : z ∈ sectorNeighborhood G.W.S smallBase radius radius :=
      sectorNeighborhood_mono G.W.S (le_max_right _ _) (min_le_left _ _) (min_le_left _ _) hz
    have hband := G.negativeInverse_opposite_middleBand hzfull k k' m side hi hiOpp hp hhalf
      htarget (hsmall z hzsmall k' m (!side) hiOpp p hp hhalf)
    let Qrad := G.negativeInverse_componentAtomJointTowerOn hadm' k' m (!side) hiOpp
      .chartRadial trivial
    let Qheight := G.negativeInverse_componentAtomJointTowerOn hadm' k' m (!side) hiOpp
      .height trivial
    let Qpair : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
        (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
        (fun x : Parameter G.W.S × PolarPoint =>
          (G.negativeInversePhysicalAtomFamily 0 .chartRadial x.1 k' x.2,
            G.negativeInversePhysicalAtomFamily 0 .height x.1 k' x.2)) :=
      smoothDirectionsProd Qrad Qheight
    have hvalue : |G.negativeInversePhysicalAtomFamily 0 .height z k' p| ≤ M := by
      have hb0 : ‖Qheight.D 0 (z, p) Fin.elim0‖ ≤
          M * parameterHeightWeight H StateAngleWord.nil.stateArity *
            t ^ (StateAngleWord.nil.angleArity + shift * StateAngleWord.nil.stateArity - 1) :=
        sourceBound 2 Qheight 0 .nil (by simp [StateAngleWord.stateArity])
          (by simp [StateAngleWord.angleArity]) Fin.elim0 (fun i => Fin.elim0 i)
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      have hzero : Qheight.D 0 (z, p) Fin.elim0 =
          G.negativeInversePhysicalAtomFamily 0 .height z k' p :=
        Qheight.zero (z, p) ⟨hz, hp⟩
      exact (Real.norm_eq_abs _).symm.trans_le
        ((congrArg norm hzero).symm.trans_le
          (n04NegativeInverse_nil_prefix (M := M) (H := H) (t := t) (shift := shift) hb0))
    have hinner (c : OrderedFinpartition n) (i : Fin c.length) :
        ‖Qpair.D (c.partSize i) (z, p) (v ∘ c.emb i)‖ ≤
          M * parameterHeightWeight H (w.restrict (c.emb i)).stateArity *
            t ^ ((w.restrict (c.emb i)).angleArity +
              shift * (w.restrict (c.emb i)).stateArity - 1) := by
      have hκ : (w.restrict (c.emb i)).stateArity ≤ K :=
        (Finset.single_le_sum (fun j _ => Nat.zero_le (w.restrict (c.emb j)).stateArity)
          (Finset.mem_univ i)).trans ((w.sum_restrict_stateArity c).le.trans hwK)
      have hβ : (w.restrict (c.emb i)).angleArity ≤ s :=
        (Finset.single_le_sum (fun j _ => Nat.zero_le (w.restrict (c.emb j)).angleArity)
          (Finset.mem_univ i)).trans ((w.sum_restrict_angleArity c).le.trans hws)
      have hr := sourceBound 0 Qrad (c.partSize i) (w.restrict (c.emb i)) hκ hβ
        (v ∘ c.emb i) (fun j => hvlow _) (fun j => hvR _) (fun j => hvphys _)
        (fun j hj => hvstate _ (by simpa only [StateAngleWord.isState_restrict] using hj))
        (fun j hj => hvspatial _ (by simpa only [StateAngleWord.isState_restrict] using hj))
      have hh := sourceBound 2 Qheight (c.partSize i) (w.restrict (c.emb i)) hκ hβ
        (v ∘ c.emb i) (fun j => hvlow _) (fun j => hvR _) (fun j => hvphys _)
        (fun j hj => hvstate _ (by simpa only [StateAngleWord.isState_restrict] using hj))
        (fun j hj => hvspatial _ (by simpa only [StateAngleWord.isState_restrict] using hj))
      change ‖((Qrad.D (c.partSize i) (z, p)).prod
        (Qheight.D (c.partSize i) (z, p))) (v ∘ c.emb i)‖ ≤ _
      rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
      exact max_le hr hh
    have hidentity (x : Parameter G.W.S × PolarPoint)
        (hx : x ∈ sectorNeighborhood G.W.S low ε' ε' ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))) :=
      G.negativeInverse_physicalAtom_opposite 0
        (sectorNeighborhood_mono G.W.S hadm'.1 hadm'.2.2.1 hadm'.2.2.1 hx.1)
        k k' m side hi hiOpp hx.2
    have hcompose (height : Bool)
        (Q : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
          (fun x : Parameter G.W.S × PolarPoint =>
            G.negativeInversePhysicalAtomFamily 0
              (if height then .height else .chartRadial) x.1 k x.2)) :
        ‖Q.D n (z, p) v‖ ≤ B * E ^ B * parameterHeightWeight H w.stateArity *
          R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
      have hnN : n ≤ s + K := by have ha := w.arity_sum; omega
      have heq : ∀ x ∈ sectorNeighborhood G.W.S low ε' ε' ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)),
          G.negativeInversePhysicalAtomFamily 0
            (if height then .height else .chartRadial) x.1 k x.2 =
              n04NegativeInverseOverlapOuter height
                (G.negativeInversePhysicalAtomFamily 0 .chartRadial x.1 k' x.2,
                  G.negativeInversePhysicalAtomFamily 0 .height x.1 k' x.2) := by
        intro x hx
        cases height
        · exact (hidentity x hx).1
        · exact (hidentity x hx).2.2
      have hcomp : ‖Q.D n (z, p) v‖ ≤
          ((2 : ℝ) ^ (s + K) * CO * (1 + M)) *
            (Fintype.card (OrderedFinpartition n) : ℝ) * (M * L) ^ n *
              parameterHeightWeight H w.stateArity *
                t ^ (w.angleArity + shift * w.stateArity - 1) :=
        n04NegativeInverse_overlapScalar_bound
          (E := Parameter G.W.S × PolarPoint)
          (U := sectorNeighborhood G.W.S low ε' ε' ×ˢ
            (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)))
          (f := fun x : Parameter G.W.S × PolarPoint =>
            (G.negativeInversePhysicalAtomFamily 0 .chartRadial x.1 k' x.2,
              G.negativeInversePhysicalAtomFamily 0 .height x.1 k' x.2))
          (g := fun x : Parameter G.W.S × PolarPoint =>
            G.negativeInversePhysicalAtomFamily 0
              (if height then .height else .chartRadial) x.1 k x.2)
          (x := (z, p)) (N := s + K) (n := n)
          (C := CO) (M := M) (H := H) (L := L) (t := t)
          Qpair Q height heq ⟨hz, hp⟩ hband hn hnN w shift hshift hCO hM hH
          (hheightL k) hL ht houter hvalue v hinner
      have hcoef : ((2 : ℝ) ^ (s + K) * CO * (1 + M)) *
          (Fintype.card (OrderedFinpartition n) : ℝ) * (M * L) ^ n ≤ B * E ^ B :=
        (hpack E hE).2 n hnN
      have hscaled := n04NegativeInverse_prefix_mono hcoef
        (parameterHeightWeight_nonneg hH w.stateArity)
        (pow_nonneg (zero_le_one.trans ht) (w.angleArity + shift * w.stateArity - 1)) hcomp
      exact hscaled.trans_eq
        (congrArg (fun r : ℝ => B * E ^ B * parameterHeightWeight H w.stateArity * r)
          (hpower (w.angleArity + shift * w.stateArity - 1)))
    have hangle
        (Q : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
          (fun x : Parameter G.W.S × PolarPoint =>
            G.negativeInversePhysicalAtomFamily 0 .chartAngleDefect x.1 k x.2)) :
        ‖Q.D n (z, p) v‖ ≤ B * E ^ B * parameterHeightWeight H w.stateArity *
          R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
      let Qsource : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
          (fun x : Parameter G.W.S × PolarPoint =>
            G.negativeInversePhysicalAtomFamily 0 .chartAngleDefect x.1 k' x.2) :=
        Q.congrOn (fun x hx => (hidentity x hx).2.1)
      exact hfinish (sourceBound 1 Qsource n w hwK hws v hvlow hvR hvphys hvstate hvspatial)
    exact n04NegativeInverseScalarAtom_jet_bound
      (E := Parameter G.W.S × PolarPoint)
      (U := sectorNeighborhood G.W.S low ε' ε' ×ˢ
        (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)))
      (f := fun atom (x : Parameter G.W.S × PolarPoint) =>
        G.negativeInversePhysicalAtomFamily 0 atom x.1 k x.2)
      (n := n) (x := (z, p)) (v := v)
      (bound := B * E ^ B * parameterHeightWeight H w.stateArity *
        R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)))
      (hcompose false) hangle (hcompose true) a J

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_componentScalars_purePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_componentScalars_purePrefix
