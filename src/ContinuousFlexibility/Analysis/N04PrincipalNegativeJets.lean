import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.N04PrincipalPositiveGeometry
import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientJetSupport

/-!
# The stationary negative principal and divided atoms

On a negative canonical piece the principal field is the fixed Airy field,
and the three divided atoms are identically zero.  Their differences from
the reference therefore have zero spatial and parameter jets.  The final
packaging lemma deliberately accepts a tower on every piece: the tower in
`CurrentJetDataOn` is quantified also on pieces outside its predicate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
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

/-- The seven principal atoms that are stationary on negative pieces. -/
def n04PrincipalNegativeStationary (a : Atom) : Prop :=
  a = .principalA ∨ a = .principalAInverse ∨ a = .principalB ∨ a = .principalC ∨
    a = .dividedA ∨ a = .dividedB ∨ a = .dividedC

/-- The open unit strip maps into a canonical interval of positive length. -/
theorem n04PrincipalNegative_unitPoint_mem {S : PhysicalSpacesData}
    (K : CanonicalData S) (m : ℕ) (hlen : K.left m < K.right m)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    canonicalUnitPoint K m q ∈ canonicalOpen S K m := by
  have hd : 0 < K.right m - K.left m := sub_pos.mpr hlen
  refine ⟨?_, mem_univ _⟩
  change K.left m < K.left m + (K.right m - K.left m) * q.1 ∧
    K.left m + (K.right m - K.left m) * q.1 < K.right m
  have hlow := mul_pos hd hq.1.1
  have hupp := mul_lt_mul_of_pos_left hq.1.2 hd
  constructor <;> linarith

/-- At every valid state, each negative stationary atom agrees with the
same atom at every other valid state.  The assertion is independent of
the material weights and does not need any reference jet estimate. -/
theorem n04PrincipalNegative_atom_eqOn {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z z' : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hz' : z' ∈ stateNeighborhood S C base ε) (hs' : stateSector S z'.1)
    (m : ℕ) (hm : K.positive m = false) (a : Atom)
    (ha : n04PrincipalNegativeStationary a) :
    EqOn (atom D T S C L K z m a) (atom D T S C L K z' m a) unitStrip := by
  intro q hq
  have hmem := n04PrincipalNegative_unitPoint_mem K m (hA.referenceBounds m).2.1 hq
  have hc := hB.2.2.2.1 z hz hs m hm (canonicalUnitPoint K m q) hmem
  have hc' := hB.2.2.2.1 z' hz' hs' m hm (canonicalUnitPoint K m q) hmem
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc.1.trans hc'.1.symm
  · exact congrArg Inv.inv (hc.1.trans hc'.1.symm)
  · exact hc.2.1.trans hc'.2.1.symm
  · exact hc.2.2.trans hc'.2.2.symm
  · simp only [atom, hm, Bool.false_eq_true, ite_false]
  · simp only [atom, hm, Bool.false_eq_true, ite_false]
  · simp only [atom, hm, Bool.false_eq_true, ite_false]

/-- Statewise equality on the open strip also annihilates every spatial
jet of the difference. -/
theorem n04PrincipalNegative_mixed_difference_zero
    {f g : PolarPoint → ℝ} (hfg : EqOn f g unitStrip)
    (i j : ℕ) (q : unitStrip) :
    mixedDerivative i j (fun y => f y - g y) q.val = 0 := by
  have hzero : EqOn (fun y => f y - g y) (fun _ => (0 : ℝ)) unitStrip :=
    fun y hy => sub_eq_zero.mpr (hfg hy)
  exact (mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    hzero i j q.property).trans (mixedDerivative_fun_zero i j q.val)

/-- A globally supplied tower has zero jets on pieces on which its scalar
family is stationary.  The estimate uses the harmless positive constant
one and no derivative loss. -/
theorem n04PrincipalNegative_currentData_of_stationary
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (href : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip ∧
      ∀ q ∈ unitStrip, f₀ m (q + (0, Real.pi)) = f₀ m q)
    (heq : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      EqOn (f z m) (f₀ m) unitStrip)
    (J : ∀ m (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val)) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  have hz0 (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => f z m y - f₀ m y) q.val = 0 :=
    n04PrincipalNegative_mixed_difference_zero (heq z hz m hm) i j q
  have hcost (m : ℕ) :
      0 ≤ (1 : ℝ) * T.E0 (T.sample (cell m)) ^ (1 : ℝ) *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (hE m) _))
      (Real.rpow_nonneg (hH m) _)
  refine ⟨?_, J, ⟨0, fun s => ⟨1, zero_lt_one, ?_⟩⟩,
    fun k => ⟨0, fun s => ⟨1, zero_lt_one, ?_⟩⟩⟩
  · intro z hz m hm
    refine ⟨(href m hm).1.congr (fun q hq => heq z hz m hm hq), ?_⟩
    intro q hq
    have hq' : q + (0, Real.pi) ∈ unitStrip := by
      refine ⟨?_, mem_univ _⟩
      change 0 < q.1 + 0 ∧ q.1 + 0 < 1
      simpa only [add_zero] using hq.1
    exact (heq z hz m hm hq').trans
      (((href m hm).2 q hq).trans (heq z hz m hm hq).symm)
  · intro z hz m hm q i j _
    rw [hz0 z hz m hm i j q, abs_zero]
    exact mul_nonneg (hcost m) (apply_nonneg _ _)
  · intro z hz v m hm q i j _
    have hzero : EqOn
        (fun x => mixedDerivative i j (fun y => f x m y - f₀ m y) q.val)
        (fun _ => 0) (sectorNeighborhood S base ε ε) :=
      fun x hx => hz0 x hx m hm i j q
    rw [(J m i j q).jets_zero_of_eqOn_zero hzero k z hz v, abs_zero]
    exact mul_nonneg (hcost m) (oneHighVariationWeight_nonneg _ _ _ _ _)

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The original seven negative stationary atoms agree with the reference
on precisely the sector neighborhood supplied by admissibility. -/
theorem n04PrincipalNegative_stationary_eqOn {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (m : ℕ) (hm : G.Neg η m) (a : Atom) (ha : n04PrincipalNegativeStationary a) :
    EqOn (G.atomFamily η a z m) (G.atomRef η a m) unitStrip := by
  have hparts := G.n04PrincipalPositive_admissible_parts h η
  have hs : stateSector (G.S η) (G.lift η z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hsref : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  exact n04PrincipalNegative_atom_eqOn hparts.1 hparts.2.1
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl) hs
    (reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1) hsref m hm a ha

/-- Negative current data for the principal and divided atoms, retaining
the global tower already constructed for the same scalar family. -/
theorem n04PrincipalNegative_currentData {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (a : Atom) (ha : n04PrincipalNegativeStationary a)
    (J : ∀ m (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood (G.S η) b ε ε)
        (fun z => mixedDerivative i j
          (fun y => G.atomFamily η a z m y - G.atomRef η a m y) q.val)) :
    G.Data η (G.Neg η) b ε (G.atomFamily η a) (G.atomRef η a) :=
  n04PrincipalNegative_currentData_of_stationary
    (G.cost_nonneg η).1 (G.cost_nonneg η).2.1 (fun m _ => href.1 m a)
    (fun _ hz m hm => G.n04PrincipalNegative_stationary_eqOn h η hz m hm a ha) J

end N04RealizationGauge

end ContinuousFlexibility.Analysis
