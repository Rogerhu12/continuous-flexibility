import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceHeightCurrentSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceHeightWordBounds
import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceSamplePrefix

/-!
# One sampled prefix for the actual source height and reciprocal

Both powers of the current height, the fixed reference powers, and the
actual source jets use one low base selected before any derivative
budget. Reindexing aligns their high seminorms and normalized powers;
the finite radial product and composition preserve the angular reserve.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_sourceHeightChoice_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ n : ℕ, n ≤ 3 → ∀ inv : Bool,
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ => radialBoundaryJet (fun p => if inv then
          (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p)⁻¹
          else n04PositiveSourceHeight (X.src i side) (W.A X.e₀)
            (liftSectorParameter W.S W.C y.1) p) (n04PositiveEndpoint i side) n y.2),
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
  let currentData := n04PositiveGeometry_sourceHeightCurrentJet_sample_prefix W X hb hε hεW hεone hflow
  let sourceData := n04PositiveGeometry_sourceJet_sample_prefix W X hb hε hεW hεone hflow
  let Bc := currentData.choose
  let Bs := sourceData.choose
  let low := max Bc Bs
  have hcl : Bc ≤ low := le_max_left _ _
  have hsl : Bs ≤ low := le_max_right _ _
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 heightData.choose
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨low, currentData.choose_spec.1.trans hcl, fun K => ?_⟩
  let currentPrefix (inv : Bool) := currentData.choose_spec.2 (if inv then 1 else -1) K
  let cc (inv : Bool) := (currentPrefix inv).choose
  let sourcePrefix := sourceData.choose_spec.2 K
  let cs := sourcePrefix.choose
  let shift := cc false + cc true + cs
  have hcc (inv : Bool) : cc inv ≤ shift := by
    cases inv <;> dsimp only [shift] <;> omega
  have hcs : cs ≤ shift := by dsimp only [shift]; omega
  refine ⟨shift, fun s => ?_⟩
  let currentOrder (inv : Bool) := (currentPrefix inv).choose_spec (s + (shift - cc inv) * K)
  let sourceOrder := sourcePrefix.choose_spec (s + (shift - cs) * K)
  let referenceOrder (inv : Bool) := n04PositiveGeometry_referenceHeightPowerJet_sample_prefix
    W X hb hε hεW hεone hflow (if inv then -1 else 1) s
  let Ac (inv : Bool) := (currentOrder inv).choose
  let Ar (inv : Bool) := (referenceOrder inv).choose
  let As := sourceOrder.choose
  have hAc (inv : Bool) : 1 ≤ Ac inv := (currentOrder inv).choose_spec.1
  have hAr (inv : Bool) : 1 ≤ Ar inv := (referenceOrder inv).choose_spec.1
  have hAs : 1 ≤ As := sourceOrder.choose_spec.1
  let B := 1 + L + Ac false + Ac true + Ar false + Ar true + As
  have hB : 1 ≤ B := by dsimp only [B]; linarith [hAc false, hAc true, hAr false, hAr true]
  have hLB : L ≤ B := by dsimp only [B]; linarith [hAc false, hAc true, hAr false, hAr true]
  have hAcB (inv : Bool) : Ac inv ≤ B := by
    cases inv <;> dsimp only [B] <;> linarith [hAc false, hAc true, hAr false, hAr true]
  have hArB (inv : Bool) : Ar inv ≤ B := by
    cases inv <;> dsimp only [B] <;> linarith [hAc false, hAc true, hAr false, hAr true]
  have hAsB : As ≤ B := by dsimp only [B]; linarith [hAc false, hAc true, hAr false, hAr true]
  let N := K + s + 1
  let boundData (j : Fin 4) := n04PositiveGeometry_sourceHeightChoice_word_bound
    W X hb hε hεW hεone hflow j.val N (by omega) L hL
  let Cj (j : Fin 4) := (boundData j).choose
  have hCj (j : Fin 4) : 1 ≤ Cj j := (boundData j).choose_spec.1
  let C := 1 + ∑ j, Cj j
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hCj j)))
  have hCC (j : Fin 4) : Cj j ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hCj j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let degree := (4 + 2 * N) * (N + 2)
  let packData := coefficientEnvelope_pack (C * B ^ degree) (B * (degree : ℝ))
  let A₀ := packData.choose
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm hctx n hn inv Q z hz hzlow θ R hR hzR
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHL : H ≤ L := (heightData.choose_spec.2 i).2.trans (le_max_right _ _)
  have hHM : H ≤ M := (hHL.trans hLB).trans
    (le_mul_of_one_le_right (zero_le_one.trans hB) (Real.one_le_rpow hE (zero_le_one.trans hB)))
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {A' : ℝ} (hA' : A' ≤ B) : A' * E ^ A' ≤ M :=
    mul_le_mul hA' (Real.rpow_le_rpow_of_exponent_le hE hA')
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hden (a : ℕ) (ha : a ≤ shift) : (s + (shift - a) * K) + a * K = s + shift * K := by
    calc
      _ = s + ((shift - a) + a) * K := by ring
      _ = _ := by rw [Nat.sub_add_cancel ha]
  have hhigh (b a : ℕ) (hbl : b ≤ low) (ha : a ≤ shift) :
      b + (s + (shift - a) * K) + a * K + 1 ≤ low + s + shift * K + 1 := by
    have he := hden a ha
    omega
  have htbudget (a : ℕ) (ha : a ≤ shift) :
      R ^ (1 / ((((s + (shift - a) * K) + a * K : ℕ) : ℝ) + 1)) = t := by rw [hden a ha]
  have hwordCost {a : ℕ} {A' : ℝ} (ha : a ≤ shift) (hA' : A' ≤ B)
      (j : ℕ) (w : StateAngleWord j) :
      A' * E ^ A' * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + a * w.stateArity) ≤
      M * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - 1) + shift * w.stateArity) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcost hA') (parameterHeightWeight_nonneg hH _))
      (pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right _ ha) _))
      (pow_nonneg (zero_le_one.trans ht) _)
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
  apply ((boundData ⟨n, by omega⟩).choose_spec.2 i side m hm hctx inv Q
    K s 1 le_rfl z hz θ P M H t hM hH hHM hHL ht shift ?_ ?_ ?_).enlarge hH (zero_le_one.trans ht)
  · intro j hj JR
    exact ((referenceOrder inv).choose_spec.2 i side m hm hctx j (hj.trans hn) JR
      K shift z hz θ P t ht).enlarge hH (zero_le_one.trans ht) (hcost (hArB inv))
  · intro j hj JC
    have hraw := (currentOrder inv).choose_spec.2 i side m hm hctx j (hj.trans hn) JC
      z hz ((hp hcl z).trans hzlow) θ R hR
      ((hp (hhigh Bc (cc inv) hcl (hcc inv)) z).trans hzR)
    intro l w hk ha v hv hvP
    have h := hraw l w hk (by omega) v hv
      (fun a => ⟨(hp hcl _).trans (hvP a).1,
        (hp (hhigh Bc (cc inv) hcl (hcc inv)) _).trans (hvP a).2⟩)
    have he := congrArg (fun q : ℝ => Ac inv * E ^ Ac inv * parameterHeightWeight H w.stateArity *
      q ^ ((w.angleArity - 1) + cc inv * w.stateArity)) (htbudget (cc inv) (hcc inv))
    exact (h.trans_eq he).trans (hwordCost (hcc inv) (hAcB inv) l w)
  · intro j hj hjn JS
    have hraw := sourceOrder.choose_spec.2 i side m hm hctx j hj (by omega) JS
      z hz ((hp hsl z).trans hzlow) θ R hR ((hp (hhigh Bs cs hsl hcs) z).trans hzR)
    intro l w hk ha v hv hvP
    have h := hraw l w hk (by omega) v hv
      (fun a => ⟨(hp hsl _).trans (hvP a).1, (hp (hhigh Bs cs hsl hcs) _).trans (hvP a).2⟩)
    have he := congrArg (fun q : ℝ => As * E ^ As * parameterHeightWeight H w.stateArity *
      q ^ ((w.angleArity - 1) + cs * w.stateArity)) (htbudget cs hcs)
    exact (h.trans_eq he).trans (hwordCost hcs hAsB l w)
  · calc
      Cj ⟨n, by omega⟩ * M ^ ((n + 1 + 2 * N) * (N + 2)) ≤ C * M ^ degree :=
        mul_le_mul (hCC _) (pow_le_pow_right₀ hM
          (Nat.mul_le_mul_right _ (by omega))) (pow_nonneg (zero_le_one.trans hM) _)
          (zero_le_one.trans hC)
      _ = (C * B ^ degree) * E ^ (B * (degree : ℝ)) := by
        dsimp only [M]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
        ring
      _ ≤ A₀ * E ^ A₀ := packData.choose_spec.2 E hE
      _ ≤ A * E ^ A := mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
