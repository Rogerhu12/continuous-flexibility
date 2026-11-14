import ContinuousFlexibility.Analysis.N04NegativeChartRootFieldBounds
import ContinuousFlexibility.Analysis.N04NegativeChartSpeedJetComposition
import ContinuousFlexibility.Analysis.N01cFlowSlotBounds

/-!
# The selected speed slots in the actual root variational equation

Interleaved state and angle directions are identified with the genuine
state derivative followed by angular differentiation. Angular slots
cost only their number of spatial derivatives. Thus the canonical
forcing heads use the physical raw prefixes already proved above.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

private theorem stateDirections_inl {n : ℕ} (w : StateAngleWord n)
    (v : Fin n → P × ℝ) :
    w.stateDirections (fun i => (((v i).1, (0 : PolarPoint)), (v i).2)) =
      fun i => (w.stateDirections v i, (0 : PolarPoint)) := by
  induction w with
  | nil => funext i; exact i.elim0
  | state w ih =>
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact congrFun (ih (Fin.tail v)) j
  | angle w ih => exact ih (Fin.tail v)

/-- The angle iteration is a spatial operation on the same function. -/
def negativeChartAngularIterate (a : ℕ) (f : N04FlowPoint → ℝ)
    (q : N04FlowPoint) : ℝ :=
  iteratedDeriv a (fun θ => f (q.1, θ)) q.2

private theorem negativeChartAngularIterate_contDiff {f : N04FlowPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℕ) :
    ContDiff ℝ ∞ (negativeChartAngularIterate a f) := by
  change ContDiff ℝ ∞ (fun q : N04FlowPoint =>
    iteratedDeriv a (fun θ => f (q.1, θ)) q.2)
  have h := contDiffOn_uncurry_iteratedDeriv
    (f := fun x θ => f (x, θ)) (V := (univ : Set (ℝ × ℝ))) isOpen_univ
    (show ContDiffOn ℝ ∞ (Function.uncurry (fun x θ => f (x, θ)))
      (univ ×ˢ univ) from hf.contDiffOn) a
  exact contDiffOn_univ.mp (by simpa only [univ_prod_univ] using h)

/-- Taking fixed unit angle directions does not enlarge the norm of
an ordinary spatial jet of the corresponding total order. -/
theorem negativeChartAngularIterate_spatialJet_le {f : N04FlowPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a j : ℕ) (q : N04FlowPoint) :
    ‖iteratedFDeriv ℝ j (negativeChartAngularIterate a f) q‖ ≤
      ‖iteratedFDeriv ℝ (j + a) f q‖ := by
  induction a generalizing j with
  | zero =>
      have he : negativeChartAngularIterate 0 f = f := by
        funext p
        simp only [negativeChartAngularIterate, iteratedDeriv_zero, Prod.eta]
      simpa only [he, Nat.add_zero] using (le_refl ‖iteratedFDeriv ℝ j f q‖)
  | succ a ih =>
      have ha := negativeChartAngularIterate_contDiff hf a
      have hb := n04NegativeGeometry_field_angle_jet_le
        (F := fun z : ℝ × N04FlowPoint => negativeChartAngularIterate a f z.2)
        (ha.comp contDiff_snd) 0 q j
      have he : negativeChartAngularIterate (a + 1) f = fun p : N04FlowPoint =>
          deriv (fun θ => negativeChartAngularIterate a f (p.1, θ)) p.2 := by
        funext p
        simp only [negativeChartAngularIterate, iteratedDeriv_succ]
      rw [he]
      have hi := ih (j + 1)
      have horder : j + 1 + a = j + (a + 1) := by omega
      rw [horder] at hi
      exact hb.trans hi

/-- The selected speed head is literally the angular derivative of the
corresponding true state derivative. The radial parameter slots are zero. -/
theorem negativeChart_speed_selected_eq
    {G : (P × PolarPoint) × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (J : ContinuousTimeSpeedTower (univ : Set (P × PolarPoint)) G)
    {n : ℕ} (b : Fin n → Bool) (v : Fin n → P) (t : ℝ) (q : N04FlowPoint) :
    let w := StateAngleWord.ofBool b
    let u := w.stateDirections (fun i => if b i then (v i, 0) else (0, 1))
    flowSpeedJointField J n (0, q.1)
      (fun i => if b i then ((v i, (0 : PolarPoint)), 0) else (0, 1)) (t, q.2) =
      negativeChartAngularIterate w.angleArity (fun p : N04FlowPoint =>
        flowParameterField G w.stateArity (0, p.1)
          (fun i => (u i, (0 : PolarPoint))) (t, p.2)) q := by
  dsimp only
  let K : SmoothDirections ((univ : Set (P × PolarPoint)) ×ˢ (univ : Set PolarPoint)) G :=
    smoothDirectionsOfJets (isOpen_univ.prod isOpen_univ)
      (fun k => iteratedFDeriv ℝ k G)
      (hasProjectiveJetsOn_of_contDiffOn (isOpen_univ.prod isOpen_univ) hG.contDiffOn)
  let R := n04Realization_jointMixedRegularity K isOpen_univ isOpen_univ
    (convex_univ.prod convex_univ)
  let Ja (a : ℕ) (θ : ℝ) := R.parameter 0 a (t, θ) (mem_univ _)
  let w := StateAngleWord.ofBool b
  let slots : Fin n → P × ℝ := fun i => if b i then (v i, 0) else (0, 1)
  have hs : (fun i => if b i then ((v i, (0 : PolarPoint)), 0) else (0, 1)) =
      fun i => (((slots i).1, (0 : PolarPoint)), (slots i).2) := by
    funext i
    cases hb : b i <;> simp only [hb, Bool.false_eq_true, if_false, if_true, slots,
      Prod.zero_eq_mk]
  have he := smoothDirections_joint_selectedSlots (J.jet t) Ja b
    (x := ((0 : P), q.1)) (mem_univ _) q.2 (fun i => (v i, (0 : PolarPoint)))
  conv at he =>
    rhs
    rw [hs, stateDirections_inl]
  have hm := n04Realization_mixedParameter_eq_joint K isOpen_univ isOpen_univ
    (convex_univ.prod convex_univ) 0 w.angleArity w.stateArity (0, q.1) (mem_univ _)
    (t, q.2) (mem_univ _) (Ja w.angleArity q.2)
    (fun i => (w.stateDirections slots i, (0 : PolarPoint)))
  have hm' : (Ja w.angleArity q.2).D w.stateArity (0, q.1)
      (fun i => (w.stateDirections slots i, (0 : PolarPoint))) =
      negativeChartAngularIterate w.angleArity (fun p : N04FlowPoint =>
        flowParameterField G w.stateArity (0, p.1)
          (fun i => (w.stateDirections slots i, (0 : PolarPoint))) (t, p.2)) q := by
    simpa only [mixedDerivative, iteratedDeriv_zero, K, smoothDirectionsOfJets,
      ← flowParameterField_eq_joint hG, negativeChartAngularIterate] using hm
  exact he.trans hm'

/-- Every spatial derivative of the original selected head is bounded
by an actual pure-state root-field jet, with exactly the angular shift. -/
theorem negativeChart_speed_selected_spatialJet_le
    {G : (P × PolarPoint) × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (J : ContinuousTimeSpeedTower (univ : Set (P × PolarPoint)) G)
    {n : ℕ} (b : Fin n → Bool) (v : Fin n → P) (t : ℝ) (j : ℕ) (q : N04FlowPoint) :
    let w := StateAngleWord.ofBool b
    let u := w.stateDirections (fun i => if b i then (v i, 0) else (0, 1))
    ‖iteratedFDeriv ℝ j (fun p : N04FlowPoint =>
      flowSpeedJointField J n (0, p.1)
        (fun i => if b i then ((v i, (0 : PolarPoint)), 0) else (0, 1)) (t, p.2)) q‖ ≤
      ‖iteratedFDeriv ℝ (j + w.angleArity) (fun p : N04FlowPoint =>
        flowParameterField G w.stateArity (0, p.1)
          (fun i => (u i, (0 : PolarPoint))) (t, p.2)) q‖ := by
  dsimp only
  let w := StateAngleWord.ofBool b
  let u := w.stateDirections (fun i => if b i then (v i, 0) else (0, 1))
  let f : N04FlowPoint → ℝ := fun p => flowParameterField G w.stateArity (0, p.1)
    (fun i => (u i, (0 : PolarPoint))) (t, p.2)
  have hf : ContDiff ℝ ∞ f :=
    (n04NegativeChart_flowParameterField_joint_contDiff hG w.stateArity
      (fun i => (u i, (0 : PolarPoint)))).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
  have he : (fun p : N04FlowPoint => flowSpeedJointField J n (0, p.1)
      (fun i => if b i then ((v i, (0 : PolarPoint)), 0) else (0, 1)) (t, p.2)) =
      negativeChartAngularIterate w.angleArity f :=
    funext (negativeChart_speed_selected_eq hG J b v t)
  rw [he]
  exact negativeChartAngularIterate_spatialJet_le hf w.angleArity j q

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.negativeChart_speed_selected_spatialJet_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.negativeChart_speed_selected_spatialJet_le
