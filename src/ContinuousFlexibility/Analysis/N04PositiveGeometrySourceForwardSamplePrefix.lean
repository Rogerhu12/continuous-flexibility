module

public import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceSamplePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryRootForwardLabelSamplePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryBudget

/-!
# Original source jets at the forward root label

The angular pullback coefficients use the source at the actual forward
label. One saved angular order pays for this substitution. Its slope
shares the same high denominator, sample and final parameter shift.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

def n04PositiveGeometry_sourceForwardJet
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (m n : ℕ)
    (y : (StateDirections W.S × ℝ) × ℝ) : PolarPoint [×n]→L[ℝ] PolarPoint :=
  n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n
    (y.1, n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side) y.2)

def n04PositiveGeometry_sourceForwardJet_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceForwardJet W X i side m n) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  exact n04PositiveGeometry_boundaryMoving_directions
    (f := n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n)
    (ψ := fun y : (StateDirections W.S × ℝ) × ℝ =>
      n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side) y.2)
    (n04PositiveGeometry_sourceJet_joint W X hb hε hεW hεone hflow
      i side m hm hctx n hn hn4)
    (n04Realization_rootLabel_forwardJointDirections W.hT W.hS hN m (!side))

theorem n04PositiveGeometry_sourceForwardJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceForwardJet W X i side m n),
      ∀ Jb : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ =>
          deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      let P := fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
        pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R
      let M := A * W.U.E0 (W.U.sample (X.cell i)) ^ A
      let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
      let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
      N04BoundaryWordBounds Q K s 1 z θ P M H t shift ∧
        N04BoundaryWordBounds Jb K s 1 z θ P M H t shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let sourceData := n04PositiveGeometry_sourceJet_sample_prefix W X hb hε hεW hεone hflow
  let labelData := n04PositiveGeometry_rootForwardLabel_sample_prefix W X hb hε hεW hflow
  let low := max sourceData.choose labelData.choose
  have hsl : sourceData.choose ≤ low := le_max_left _ _
  have hll : labelData.choose ≤ low := le_max_right _ _
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp := sectorPairGrading_monotone W.S
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨low, sourceData.choose_spec.1.trans hsl, fun K => ?_⟩
  let sourcePrefix := sourceData.choose_spec.2 K
  let labelPrefix := labelData.choose_spec.2 K
  let cs := sourcePrefix.choose
  let cl := labelPrefix.choose
  let c := max cs cl
  have hcs : cs ≤ c := le_max_left _ _
  have hcl : cl ≤ c := le_max_right _ _
  refine ⟨c + 1, fun s => ?_⟩
  let sourceOrder := sourcePrefix.choose_spec (s + (c + 1 - cs) * K)
  let labelOrder := labelPrefix.choose_spec (s + (c + 1 - cl) * K)
  let As := sourceOrder.choose
  let Al := labelOrder.choose
  let L := max 1 heightData.choose
  let B := As + Al + L
  have hAs : 1 ≤ As := sourceOrder.choose_spec.1
  have hAl : 1 ≤ Al := labelOrder.choose_spec.1
  have hL : 1 ≤ L := le_max_left _ _
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hAsB : As ≤ B := by dsimp only [B]; linarith
  have hAlB : Al ≤ B := by dsimp only [B]; linarith
  have hLB : L ≤ B := by dsimp only [B]; linarith
  let movingData (j : Fin 5) := n04PositiveGeometry_boundaryMoving_saved_word_bound
    (E := StateDirections W.S × ℝ) (F := PolarPoint [×j.val]→L[ℝ] PolarPoint) K s
  let C := 1 + ∑ j : Fin 5, (movingData j).choose
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (movingData j).choose_spec.1))
  have hjC (j : Fin 5) : (movingData j).choose ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (movingData j).choose_spec.1)
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)
  let degree := 2 * (K + s + 1) + 2
  let packData := coefficientEnvelope_pack (C * B ^ degree) (B * (degree : ℝ))
  let A₀ := packData.choose
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm hctx n hn hn4 Q Jb z hz hzlow θ R hR hzR
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + (c + 1) * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + (c + 1) * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hBM : B ≤ M := le_mul_of_one_le_right (zero_le_one.trans hB)
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have hM : 1 ≤ M := hB.trans hBM
  have hHM : H ≤ M := (heightData.choose_spec.2 i).2.trans
    ((le_max_right _ _).trans (hLB.trans hBM))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {a : ℝ} (ha : a ≤ B) : a * E ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hspan (a : ℕ) (ha : a ≤ c) : s + K ≤ s + (c + 1 - a) * K := by
    exact Nat.add_le_add_left (by
      simpa only [one_mul] using Nat.mul_le_mul_right K (show 1 ≤ c + 1 - a by omega)) s
  have hhigh (l a : ℕ) (hl : l ≤ low) (ha : a ≤ c) :
      l + (s + (c + 1 - a) * K) + a * K + 1 ≤ low + s + (c + 1) * K + 1 := by
    have he := n04PositiveGeometry_prefix_horizon s K a (c + 1) (by omega)
    omega
  have hpower (a : ℕ) (ha : a ≤ c) :
      R ^ (1 / ((((s + (c + 1 - a) * K) + a * K : ℕ) : ℝ) + 1)) = t :=
    congrArg (fun q : ℕ => R ^ (1 / ((q : ℝ) + 1)))
      (n04PositiveGeometry_prefix_horizon s K a (c + 1) (by omega))
  let JF := n04PositiveGeometry_sourceJet_joint W X hb hε hεW hεone hflow
    i side m hm hctx n hn hn4
  let Jβ := n04Realization_rootLabel_forwardJointDirections W.hT W.hS hN m (!side)
  let β := n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m (!side) θ
  have hsource := sourceOrder.choose_spec.2 i side m hm hctx n hn hn4 JF z hz
    ((hp hsl z).trans hzlow) β R hR ((hp (hhigh _ _ hsl hcs) z).trans hzR)
  have hF : N04BoundaryWordBounds JF K (s + K) 1 z β P M H t c :=
    hsource.mono_budget le_rfl (hspan cs hcs)
      (fun v hv => ⟨(hp hsl v).trans hv.1, (hp (hhigh _ _ hsl hcs) v).trans hv.2⟩)
      (zero_le_one.trans hM) hH ht (hcost hAsB) (hpower cs hcs) hcs
  have hlabel := labelOrder.choose_spec.2 i side m hm Jβ Jb z hz
    ((hp hll z).trans hzlow) θ R hR ((hp (hhigh _ _ hll hcl) z).trans hzR)
  have hβ : N04BoundaryPositiveWordBounds Jβ K (s + K) 1 z θ P M H t c :=
    hlabel.1.mono_budget le_rfl (hspan cl hcl)
      (fun v hv => ⟨(hp hll v).trans hv.1, (hp (hhigh _ _ hll hcl) v).trans hv.2⟩)
      (zero_le_one.trans hM) hH ht (hcost hAlB) (hpower cl hcl) hcl
  have hb' : N04BoundaryWordBounds Jb K s 1 z θ P M H t (c + 1) :=
    hlabel.2.mono_budget le_rfl ((Nat.le_add_right s K).trans (hspan cl hcl))
      (fun v hv => ⟨(hp hll v).trans hv.1, (hp (hhigh _ _ hll hcl) v).trans hv.2⟩)
      (zero_le_one.trans hM) hH ht (hcost hAlB) (hpower cl hcl) (by omega)
  have hfinal : C * M ^ degree ≤ A * E ^ A := by
    calc
      _ = (C * B ^ degree) * E ^ (B * (degree : ℝ)) := by
        dsimp only [M]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
        ring
      _ ≤ A₀ * E ^ A₀ := packData.choose_spec.2 E hE
      _ ≤ A * E ^ A := mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  have hbase : M ≤ C * M ^ degree := by
    have hpow : M ≤ M ^ degree := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ degree by dsimp only [degree]; omega)
    exact hpow.trans (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hC)
  let idx : Fin 5 := ⟨n, by omega⟩
  have hmove := (movingData idx).choose_spec.2 JF Jβ Q z hz θ (p low)
    (p (low + s + (c + 1) * K + 1)) R (zero_le_one.trans hR)
    M H t hM hH hHM ht c hF hβ
  exact ⟨hmove.enlarge hH (zero_le_one.trans ht)
    ((mul_le_mul_of_nonneg_right (hjC idx) (pow_nonneg (zero_le_one.trans hM) _)).trans hfinal),
    hb'.enlarge hH (zero_le_one.trans ht) (hbase.trans hfinal)⟩

end ContinuousFlexibility.Analysis
