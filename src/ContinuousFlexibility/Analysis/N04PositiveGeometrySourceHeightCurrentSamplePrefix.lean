module

public import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceHeightJets
public import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseLabelSamplePrefix

/-!
# Sampled current height jets at the actual source point

The stored height and inverse label share one low base. Their angular
horizons are reindexed to the same normalized sampling radius before
the moving-angle rule is applied, retaining one angular reserve.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_sourceHeightCurrentJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ γ : ℝ, ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ n : ℕ, n ≤ 3 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceHeightCurrentJet W X i side m γ n),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  classical
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let heightData := n04PositiveGeometry_storedHeightPowerJet_sample_prefix W X hb hε hεW hεone hflow
  let labelData := n04PositiveGeometry_rootInverseLabel_sample_prefix W X hb hε hεW hflow
  let Bh : ℕ := heightData.choose
  let Bl : ℕ := labelData.choose
  let low := max Bh Bl
  have hhl : Bh ≤ low := le_max_left _ _
  have hll : Bl ≤ low := le_max_right _ _
  let boundedHeight := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 boundedHeight.choose
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨low, heightData.choose_spec.1.trans hhl, fun γ K => ?_⟩
  let heightPrefix := heightData.choose_spec.2 γ K
  let labelPrefix := labelData.choose_spec.2 K
  let ch := heightPrefix.choose
  let cl := labelPrefix.choose
  let c := ch + cl
  have hch : ch ≤ c := by dsimp only [c]; omega
  have hcl : cl ≤ c := by dsimp only [c]; omega
  refine ⟨c + 1, fun s => ?_⟩
  let sh := s + (c + 1 - ch) * K
  let sl := s + (c + 1 - cl) * K
  let heightOrder := heightPrefix.choose_spec sh
  let labelOrder := labelPrefix.choose_spec sl
  let Ah := heightOrder.choose
  let Al := labelOrder.choose
  let B := max Ah (max Al L)
  have hB : 1 ≤ B := heightOrder.choose_spec.1.trans (le_max_left _ _)
  have hAhB : Ah ≤ B := le_max_left _ _
  have hAlB : Al ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hLB : L ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let movingData (j : Fin 4) := n04PositiveGeometry_boundaryMoving_saved_word_bound
    (E := StateDirections W.S × ℝ) (F := PolarPoint [×j.val]→L[ℝ] ℝ) K s
  let Cj : Fin 4 → ℝ := fun j => (movingData j).choose
  have hCj (j : Fin 4) : 1 ≤ Cj j := (movingData j).choose_spec.1
  let C : ℝ := 1 + ∑ j, Cj j
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hCj j)))
  have hCC (j : Fin 4) : Cj j ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hCj j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let degree := 2 * (K + s + 1) + 2
  let packData := coefficientEnvelope_pack (C * B ^ degree) (B * (degree : ℝ))
  let A₀ := packData.choose
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm hctx n hn Q z hz hzlow θ R hR hzR
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + (c + 1) * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + (c + 1) * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (boundedHeight.choose_spec.2 i).1
  have hHM : H ≤ M := ((boundedHeight.choose_spec.2 i).2.trans
    ((le_max_right _ _).trans hLB)).trans
      (le_mul_of_one_le_right (zero_le_one.trans hB) (Real.one_le_rpow hE (zero_le_one.trans hB)))
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {Q : ℝ} (hQ : Q ≤ B) : Q * E ^ Q ≤ M :=
    mul_le_mul hQ (Real.rpow_le_rpow_of_exponent_le hE hQ)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hden (a : ℕ) (ha : a ≤ c) : (s + (c + 1 - a) * K) + a * K = s + (c + 1) * K := by
    calc
      _ = s + ((c + 1 - a) + a) * K := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : a ≤ c + 1)]
  have hspan (a : ℕ) (ha : a ≤ c) : s + K ≤ s + (c + 1 - a) * K := by
    have hmul := Nat.mul_le_mul_right K (show 1 ≤ c + 1 - a by omega)
    simpa only [one_mul] using Nat.add_le_add_left hmul s
  have hhigh (b a : ℕ) (hbl : b ≤ low) (ha : a ≤ c) :
      b + (s + (c + 1 - a) * K) + a * K + 1 ≤ low + s + (c + 1) * K + 1 := by
    have he := hden a ha
    omega
  have htbudget (a : ℕ) (ha : a ≤ c) :
      R ^ (1 / ((((s + (c + 1 - a) * K) + a * K : ℕ) : ℝ) + 1)) = t := by
    rw [hden a ha]
  have hwordCost {a : ℕ} {A' : ℝ} (ha : a ≤ c) (hA' : A' ≤ B)
      (j : ℕ) (w : StateAngleWord j) :
      A' * E ^ A' * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + a * w.stateArity) ≤
      M * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + c * w.stateArity) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcost hA') (parameterHeightWeight_nonneg hH _))
      (pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right _ ha) _))
      (pow_nonneg (zero_le_one.trans ht) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
  have hrad := n04PositiveGeometry_source_root_eq W X i side m hm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  let JH := n04PositiveGeometry_storedHeightPowerJet_joint W.hT W.hS hN hεone hflow
    hctx hr hroot γ n hn
  let Jα := n04Realization_rootLabel_inverseJointDirections W.hT W.hS hN m (!side)
  let Jb : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ => deriv
        (Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side))) y.2) :=
    (smoothDirections_angularIterate Jα 1).congr (fun _ _ => by simp only [iteratedDeriv_one])
  let η := Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m (!side)) θ
  have houterRaw := heightOrder.choose_spec.2 i side m hm (W.A X.e₀) hctx n hn JH
    z hz ((hp hhl z).trans hzlow) η R hR ((hp (hhigh Bh ch hhl hch) z).trans hzR)
  have houter : N04BoundaryWordBounds JH K (s + K) 1 z η P M H t c := by
    intro j w hk ha v hv hvP
    have h := houterRaw j w hk (ha.trans (Nat.add_le_add_right (hspan ch hch) 1)) v hv
      (fun l => ⟨(hp hhl _).trans (hvP l).1, (hp (hhigh Bh ch hhl hch) _).trans (hvP l).2⟩)
    have he := congrArg (fun q : ℝ => Ah * E ^ Ah * parameterHeightWeight H w.stateArity *
      q ^ ((w.angleArity - 1) + ch * w.stateArity)) (htbudget ch hch)
    exact (h.trans_eq he).trans (hwordCost hch hAhB j w)
  have hlabel := labelOrder.choose_spec.2 i side m hm Jα Jb
    z hz ((hp hll z).trans hzlow) θ R hR ((hp (hhigh Bl cl hll hcl) z).trans hzR)
  have hinner : N04BoundaryPositiveWordBounds Jα K (s + K) 1 z θ P M H t c := by
    intro j hj w hk ha v hv hvP
    have h := hlabel.1 j hj w hk (ha.trans (Nat.add_le_add_right (hspan cl hcl) 1)) v hv
      (fun l => ⟨(hp hll _).trans (hvP l).1, (hp (hhigh Bl cl hll hcl) _).trans (hvP l).2⟩)
    have he := congrArg (fun q : ℝ => Al * E ^ Al * parameterHeightWeight H w.stateArity *
      q ^ ((w.angleArity - 1) + cl * w.stateArity)) (htbudget cl hcl)
    exact (h.trans_eq he).trans (hwordCost hcl hAlB j w)
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  let JO := n04PositiveGeometry_boundaryMoving_directions JH Jα
  have hmoving := (movingData ⟨n, by omega⟩).choose_spec.2 JH Jα JO z hz θ
    (p low) (p (low + s + (c + 1) * K + 1)) R (zero_le_one.trans hR)
    M H t hM hH hHM ht c houter hinner
  have hactual : N04BoundaryWordBounds Q K s 1 z θ P
      (Cj ⟨n, by omega⟩ * M ^ degree) H t (c + 1) := by
    apply hmoving.congr hz
    intro y hy
    have hzW := stateNeighborhood_mono W.S W.C hb hεW
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy.1 le_rfl)
    have hs := hN.2.2.1.liftSectorParameter_sector y.1
    have hpoint := n04PositiveGeometry_source_endpoint_value W X i side m hm hzW hs y.2
    have hidx : (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1) =
        (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2) := by
      cases side <;> rfl
    simpa only [n04PositiveGeometry_sourceHeightCurrentJet,
      n04PositiveGeometry_storedHeightPowerJet, hidx, hrad] using
      congrArg (fun p => iteratedFDeriv ℝ n
        (fun q => (W.A X.e₀).height (liftSectorParameter W.S W.C y.1)
          (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2) q ^ γ) p) hpoint.symm
  apply hactual.enlarge hH (zero_le_one.trans ht)
  calc
    Cj ⟨n, by omega⟩ * M ^ degree ≤ C * M ^ degree :=
      mul_le_mul_of_nonneg_right (hCC _) (pow_nonneg (zero_le_one.trans hM) _)
    _ = (C * B ^ degree) * E ^ (B * (degree : ℝ)) := by
      dsimp only [M]
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
      ring
    _ ≤ A₀ * E ^ A₀ := packData.choose_spec.2 E hE
    _ ≤ A * E ^ A := mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
