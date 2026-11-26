import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace IncrementCycles

noncomputable section

inductive S | E | P | R deriving DecidableEq, Repr
open S
@[simp] theorem E_ne_P : E ≠ P := by decide
@[simp] theorem E_ne_R : E ≠ R := by decide
@[simp] theorem P_ne_E : P ≠ E := by decide
@[simp] theorem P_ne_R : P ≠ R := by decide
@[simp] theorem R_ne_E : R ≠ E := by decide
@[simp] theorem R_ne_P : R ≠ P := by decide

def flip : S → S
  | E => R | P => P | R => E

@[simp] theorem flip_flip (s : S) : flip (flip s) = s := by cases s <;> rfl

def reverseWord (w : List S) : List S := w.reverse.map flip

theorem reverseWord_involution (w : List S) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, ← List.map_reverse, List.map_map, Function.comp_def]

abbrev Pair := S → S → ℝ
def reversePair (J : Pair) : Pair := fun i j => J (flip j) (flip i)
def row (J : Pair) (s : S) := J s E + J s P + J s R
def col (J : Pair) (s : S) := J E s + J P s + J R s
def stationary (J : Pair) := ∀ s, row J s = col J s
def mass (J : Pair) := row J E + row J P + row J R
def q1 (J : Pair) := J E E - J R R
def q2 (J : Pair) := J E P - J P R
def q3 (J : Pair) := J P E - J R P

theorem reversePair_involution (J : Pair) : reversePair (reversePair J) = J := by
  funext i j
  simp [reversePair]

theorem stationary_q3 (J : Pair) (h : stationary J) : q3 J = q2 J := by
  have hp := h P
  unfold row col at hp
  unfold q3 q2
  linarith

def oddMatrix (a b : ℝ) : Pair
  | E,E => a | E,P => b | E,R => 0
  | P,E => b | P,P => 0 | P,R => -b
  | R,E => 0 | R,P => -b | R,R => -a

theorem odd_matrix (J : Pair) (h : stationary J) (i j : S) :
    J i j - reversePair J i j = oddMatrix (q1 J) (q2 J) i j := by
  have hp := h P
  unfold row col at hp
  cases i <;> cases j <;> simp [reversePair, flip, oddMatrix, q1, q2] <;> linarith

theorem pair_iff (J : Pair) (h : stationary J) :
    reversePair J = J ↔ q1 J = 0 ∧ q2 J = 0 := by
  constructor
  · intro he
    constructor
    · have he' := congrFun (congrFun he E) E
      simp [reversePair, flip] at he'
      unfold q1
      linarith
    · have he' := congrFun (congrFun he E) P
      simp [reversePair, flip] at he'
      unfold q2
      linarith
  · rintro ⟨h1,h2⟩
    funext i j
    have hs := odd_matrix J h i j
    rw [h1,h2] at hs
    cases i <;> cases j <;> simp [oddMatrix] at hs <;> linarith

theorem marginal_difference (J : Pair) (h : stationary J) :
    q1 J + q2 J = row J E - row J R := by
  have he := h E
  have hp := h P
  unfold row col at he hp
  unfold row
  unfold q1 q2
  linarith

theorem q_order_even (J : Pair) (h : stationary J) :
    q1 (fun i j => J j i) = q1 J ∧ q2 (fun i j => J j i) = q2 J :=
  ⟨rfl, stationary_q3 J h⟩

-- Explicit affine chart for the normalized stationary ambient space.
def chart (a b c d e f : ℝ) : Pair
  | E,E => a | E,P => b | E,R => c
  | P,E => d | P,P => e | P,R => f
  | R,E => b+c-d | R,P => d+e+f-(b+e) | R,R => 1-(a+b+c+d+e+f+(b+c-d)+(d+e+f-(b+e)))

theorem chart_law (a b c d e f : ℝ) :
    stationary (chart a b c d e f) ∧ mass (chart a b c d e f) = 1 := by
  constructor
  · intro s
    cases s <;> simp [row, col, chart] <;> ring
  · simp [mass, row, chart]
    ring

theorem chart_reconstruct (J : Pair) (h : stationary J) (hm : mass J = 1) :
    chart (J E E) (J E P) (J E R) (J P E) (J P P) (J P R) = J := by
  have he := h E
  have hp := h P
  unfold row col at he hp
  unfold mass row at hm
  funext i j
  cases i <;> cases j <;> simp only [chart] <;> linarith

theorem chart_injective {a b c d e f a' b' c' d' e' f' : ℝ}
    (h : chart a b c d e f = chart a' b' c' d' e' f') :
    a=a' ∧ b=b' ∧ c=c' ∧ d=d' ∧ e=e' ∧ f=f' :=
  ⟨congrFun (congrFun h E) E, congrFun (congrFun h E) P, congrFun (congrFun h E) R,
   congrFun (congrFun h P) E, congrFun (congrFun h P) P, congrFun (congrFun h P) R⟩

theorem odd_chart (J : Pair) (h : stationary J) (ht : reversePair J = fun i j => -J i j) :
    J = oddMatrix (q1 J / 2) (q2 J / 2) := by
  funext i j
  have hh := odd_matrix J h i j
  rw [ht] at hh
  cases i <;> cases j <;> simp [oddMatrix] at hh ⊢ <;> linarith

theorem odd_chart_coordinates (a b : ℝ) :
    stationary (oddMatrix a b) ∧ reversePair (oddMatrix a b) = (fun i j => -oddMatrix a b i j) ∧
    oddMatrix a b E E = a ∧ oddMatrix a b E P = b := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro s
    cases s <;> simp [row,col,oddMatrix]
  · funext i j
    cases i <;> cases j <;> simp [reversePair, flip, oddMatrix]

def numerator (J : Pair) := J E P * J P R * J R E
def denominator (J : Pair) := J P E * J R P * J E R
def affinity (J : Pair) := Real.log (numerator J / denominator J)

theorem affinity_even (J : Pair) :
    numerator (reversePair J) = numerator J ∧ denominator (reversePair J) = denominator J ∧
    affinity (reversePair J) = affinity J := by
  have hn : numerator (reversePair J) = numerator J := by
    unfold numerator reversePair flip
    ring
  have hd : denominator (reversePair J) = denominator J := by
    unfold denominator reversePair flip
    ring
  exact ⟨hn, hd, by simp [affinity, hn, hd]⟩

def indicator (a b : S) : ℤ := if a = b then 1 else 0
def count (i j : S) (start : S) : List S → ℤ
  | [] => 0
  | next :: tail => indicator start i * indicator next j + count i j next tail

def endpoint {A : Type*} (start : A) : List A → A
  | [] => start
  | next :: tail => endpoint next tail

theorem finite_window (start : S) (tail : List S) :
    (count E P start tail - count P R start tail) -
    (count P E start tail - count R P start tail) =
      indicator (endpoint start tail) P - indicator start P := by
  induction tail generalizing start with
  | nil => simp [count, endpoint]
  | cons next tail ih =>
    have h := ih next
    have step :
        (indicator start E * indicator next P - indicator start P * indicator next R) -
        (indicator start P * indicator next E - indicator start R * indicator next P) =
        indicator next P - indicator start P := by
      cases start <;> cases next <;> decide
    simp only [count, endpoint]
    omega


def productPairs {A : Type*} (k : A → A → ℝ) (s : A) : List A → ℝ
  | [] => 1
  | a :: w => k s a * productPairs k a w

theorem productPairs_snoc {A : Type*} (k : A → A → ℝ) (a b : A) (w : List A) :
    productPairs k a (w ++ [b]) = productPairs k a w * k (endpoint a w) b := by
  induction w generalizing a with
  | nil => simp [productPairs, endpoint]
  | cons c w ih => simp [productPairs, endpoint, ih, mul_assoc]

section GeneralReversal
variable {A : Type*}
def reverseMapped (par : A → A) (w : List A) := w.reverse.map par

theorem reverseMapped_cons (par : A → A) (a : A) (w : List A) :
    reverseMapped par (a :: w) = reverseMapped par w ++ [par a] := by simp [reverseMapped]

theorem reverseMapped_head (par : A → A) (a : A) (w : List A) :
    ∃ t, reverseMapped par (a :: w) = par (endpoint a w) :: t := by
  induction w generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b w ih =>
    obtain ⟨t, ht⟩ := ih b
    exact ⟨t ++ [par a], by rw [reverseMapped_cons, ht]; rfl⟩

theorem endpoint_snoc (a b : A) (w : List A) : endpoint a (w ++ [b]) = b := by
  induction w generalizing a with
  | nil => rfl
  | cons c w ih => exact ih c

theorem reversal_flux_general (par : A → A) (k : A → A → ℝ) (p : A → ℝ)
    (h : ∀ i j, p i * k i j = p (par j) * k (par j) (par i))
    (hp : ∀ i, p (par i) = p i)
    (a : A) (w : List A) :
    p a * productPairs k a w =
      p (par (endpoint a w)) *
      productPairs k (par (endpoint a w)) (reverseMapped par (a :: w)).tail := by
  induction w generalizing a with
  | nil => simpa [productPairs, endpoint, reverseMapped] using (hp a).symm
  | cons b w ih =>
    obtain ⟨t,ht⟩ := reverseMapped_head par b w
    have revlast : endpoint (par (endpoint b w)) t = par b := by
      cases w with
      | nil =>
        have : t = [] := by simpa [reverseMapped,endpoint] using ht.symm
        simp [this, endpoint]
      | cons c w =>
        obtain ⟨u,hu⟩ := reverseMapped_head par c w
        have ht' : t = u ++ [par b] := by
          have : reverseMapped par (b :: c :: w) =
              par (endpoint c w) :: (u ++ [par b]) := by rw [reverseMapped_cons, hu]; rfl
          rw [ht] at this
          exact (List.cons.inj this).2
        rw [ht', endpoint_snoc]
    have hi := ih b
    rw [ht] at hi
    simp only [List.tail_cons] at hi
    rw [reverseMapped_cons, ht]
    simp only [List.cons_append, List.tail_cons, productPairs, endpoint,
      productPairs_snoc, revlast]
    calc
      p a * (k a b * productPairs k b w) =
          (p a * k a b) * productPairs k b w := by ring
      _ = p b * productPairs k b w * k (par b) (par a) := by rw [h a b, hp b]; ring
      _ = _ := by rw [hi]; ring

end GeneralReversal

theorem reversal_flux (k : Pair) (p : S → ℝ)
    (h : ∀ i j, p i * k i j = p (flip j) * k (flip j) (flip i))
    (hp : ∀ i, p (flip i) = p i)
    (a : S) (w : List S) :
    p a * productPairs k a w =
      p (flip (endpoint a w)) * productPairs k (flip (endpoint a w)) (reverseWord (a :: w)).tail :=
  reversal_flux_general flip k p h hp a w

def em (η : ℝ) (i j : S) : ℝ := (if i = j then 1-η else 0) + η/3
abbrev Readout := S → ℝ

def cyc2 (lag : Nat) (f g : Readout) : ℝ :=
  if lag = 1 then
    (f E*g P+f P*g R+f R*g E+f E*g R+f R*g P+f P*g E)/6
  else
    (f E*g R+f P*g E+f R*g R+f E*g P+f R*g E+f P*g P)/6

def cyc3 (f g h : Readout) : ℝ :=
  (f E*g P*h R+f P*g R*h E+f R*g E*h R+f E*g R*h P+f R*g P*h E+f P*g E*h P)/6

def mean (f : Readout) : ℝ := (f E + f P + f R)/3
def directed2 (ρ : ℝ) (f g : Readout) : ℝ :=
  (1-ρ)*cyc2 1 f g+ρ*mean f*mean g

-- Condition on no reset, a reset on either edge, or on both edges.
def directed3 (ρ : ℝ) (f g h : Readout) : ℝ :=
  (1-ρ)^2*cyc3 f g h + ρ*(1-ρ)*(mean f*cyc2 1 g h + cyc2 1 f g*mean h) +
    ρ^2*mean f*mean g*mean h

def lag2 (ρ : ℝ) (f h : Readout) : ℝ :=
  (1-ρ)^2*cyc2 2 f h+(1-(1-ρ)^2)*mean f*mean h

def ctrl2 (ρ : ℝ) (f g : Readout) : ℝ :=
  (directed2 ρ f g+directed2 ρ (g ∘ flip) (f ∘ flip))/2

def ctrl3 (ρ : ℝ) (f g h : Readout) : ℝ :=
  (1-ρ)^2*(cyc3 f g h + cyc3 (h ∘ flip) (g ∘ flip) (f ∘ flip))/2 +
  ρ*(1-ρ)*(mean f*ctrl2 0 g h + ctrl2 0 f g*mean h) + ρ^2*mean f*mean g*mean h

def ctrlLag2 (ρ : ℝ) (f h : Readout) : ℝ :=
  (1-ρ)^2*(cyc2 2 f h + cyc2 2 (h ∘ flip) (f ∘ flip))/2 +
  (1-(1-ρ)^2)*mean f*mean h

theorem eq5 (η : ℝ) :
    cyc3 (em η · P) (em η · R) (em η · E) =
      (1-η)^3/6+(1-η)^2*(η/3)/2+(1-η)*(η/3)^2+(η/3)^3 ∧
    cyc3 (em η · R) (em η · E) (em η · P) =
      (1-η)^2*(η/3)/3+(1-η)*(η/3)^2+(η/3)^3 := by
  constructor <;> simp [cyc3, em] <;> ring

theorem eq6_7 (η : ℝ) :
    cyc3 (em η · P) (em η · R) (em η · E) -
      cyc3 (em η · R) (em η · E) (em η · P) = (1-η)^2*(3-2*η)/18 ∧
    cyc2 2 (em η · P) (em η · E) - cyc2 2 (em η · R) (em η · P) =
      (1-η)^2/6 := by
  constructor <;> simp [cyc3,cyc2,em] <;> ring

theorem same_adjacent (ρ : ℝ) (f g : Readout) :
    directed2 ρ f g = ctrl2 ρ f g := by
  simp [ctrl2,directed2,cyc2,mean,flip]
  ring

theorem eq10 (ρ η : ℝ) :
    directed3 ρ (em η · P) (em η · R) (em η · E) -
      directed3 ρ (em η · R) (em η · E) (em η · P) =
      (1-ρ)^2*(1-η)^2*(3-2*η)/18 ∧
    lag2 ρ (em η · P) (em η · E) - lag2 ρ (em η · R) (em η · P) =
      (1-ρ)^2*(1-η)^2/6 := by
  constructor <;> simp [directed3,lag2,cyc3,cyc2,mean,em] <;> ring

def swapped (η α β : ℝ) (i : S) : S → ℝ
  | E => (1-α)*em η i E+β*em η i R
  | P => em η i P
  | R => α*em η i E+(1-β)*em η i R

theorem eq11 (ρ η α β : ℝ) :
    let e := (swapped η α β · E)
    let p := (swapped η α β · P)
    let r := (swapped η α β · R)
    let κ := (1-ρ)^2*(1-η)^2
    let δ := α-β
    let s := α+β
    ctrl3 ρ p r e - ctrl3 ρ r e p = 0 ∧
    ctrlLag2 ρ p e - ctrlLag2 ρ r p = -δ*(4-κ)/18 ∧
    directed3 ρ p r e - directed3 ρ r e p = (1-s)*κ*(3-2*η)/18 ∧
    lag2 ρ p e - lag2 ρ r p = (1-s)*κ/6-δ*(4-κ)/18 := by
  dsimp only
  simp only [ctrl3,ctrlLag2,ctrl2,directed3,directed2,lag2,cyc3,cyc2,mean,swapped,em,
    Function.comp_def,flip,reduceCtorEq,if_true,if_false, Nat.reduceEqDiff]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

theorem swapped_marginal (η α β : ℝ) :
    mean (swapped η α β · E) - mean (swapped η α β · R) = -2*(α-β)/3 := by
  simp [mean, swapped, em]
  ring

theorem triple_positive {η ρ : ℝ} (he : η < 1) (hr : ρ < 1) :
    (1-ρ)^2*(1-η)^2*(3-2*η)/18 > 0 := by
  exact div_pos (mul_pos (mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _))
    (by linarith)) (by norm_num)


def threeSum (f : Fin 3 → ℝ) := f ⟨0,by decide⟩ + f ⟨1,by decide⟩ + f ⟨2,by decide⟩

def chainStep (i j : Fin 3) : ℝ :=
  match i.val,j.val with
  | 0,0 => 7/10 | 0,1 => 3/10 | 1,0 => 1/10 | 1,1 => 3/10
  | 1,2 => 6/10 | 2,1 => 2/10 | 2,2 => 8/10 | _,_ => 0

def chainPi (i : Fin 3) : ℝ := match i.val with
  | 0 => 1/13 | 1 => 3/13 | _ => 9/13

def signStep (i j : Fin 3) : S :=
  if i.val < j.val then E else if i.val = j.val then P else R

def reversibleExample : Pair := fun a b =>
  threeSum fun i => threeSum fun j => threeSum fun k =>
    if signStep i j = a ∧ signStep j k = b then
      chainPi i * chainStep i j * chainStep j k else 0

theorem reversible_parent :
    (∀ i j, chainPi i * chainStep i j = chainPi j * chainStep j i) ∧
    (∀ i, threeSum (chainStep i) = 1) ∧ threeSum chainPi = 1 := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [chainPi,chainStep]
  · intro i
    fin_cases i <;> norm_num [threeSum,chainStep]
  · norm_num [threeSum,chainPi]

theorem reversible_counterexample :
    reversePair reversibleExample = reversibleExample ∧
    numerator reversibleExample / denominator reversibleExample = 7803/625 ∧
    0 < affinity reversibleExample := by
  have h : numerator reversibleExample / denominator reversibleExample = 7803/625 := by
    norm_num [numerator,denominator,reversibleExample,threeSum,signStep,chainPi,chainStep,reduceCtorEq]
  refine ⟨?_,h,?_⟩
  · funext i j
    cases i <;> cases j <;> norm_num [reversePair,flip,reversibleExample,threeSum,
      signStep,chainPi,chainStep,reduceCtorEq]
  · rw [affinity,h]
    exact Real.log_pos (by norm_num)

def ringP : Readout
  | E => 1/2 | P => 1/4 | R => 1/4

def iidRing : Pair := fun i j => ringP i * ringP j

theorem ring_counterexample :
    q1 iidRing = 3/16 ∧ q2 iidRing = 1/16 ∧ affinity iidRing = 0 := by
  norm_num [q1,q2,affinity,numerator,denominator,iidRing,ringP]

theorem ring_mean_log_ratio :
    (1/2 : ℝ)*Real.log 2+(1/4)*Real.log (1/2)=(Real.log 2)/4 := by
  rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

def equalMarginal : Pair
  | E,E => 5/36 | E,P => 3/36 | E,R => 4/36
  | P,E => 3/36 | P,P => 4/36 | P,R => 5/36
  | R,E => 4/36 | R,P => 5/36 | R,R => 3/36

theorem marginal_counterexample :
    stationary equalMarginal ∧ (∀ i, row equalMarginal i = 1/3) ∧
    q1 equalMarginal = 1/18 ∧ q2 equalMarginal = -1/18 ∧ affinity equalMarginal = 0 := by
  refine ⟨?_,?_,?_⟩
  · intro i
    cases i <;> norm_num [row,col,equalMarginal]
  · intro i
    cases i <;> norm_num [row,equalMarginal]
  · norm_num [q1,q2,affinity,numerator,denominator,equalMarginal]

theorem conjugate_kl_term {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    p * Real.log (p/r) + r * Real.log (r/p) = (p-r)*Real.log (p/r) := by
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hr), Real.log_div (ne_of_gt hr) (ne_of_gt hp)]
  ring

theorem pair_kl_nonneg {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    0 ≤ (p-r)*Real.log (p/r) := by
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hr)]
  rcases le_total p r with h|h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn hp hr h))
  · exact mul_nonneg (sub_nonneg.mpr h)
      (sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hr hp h))

theorem pair_kl_positive {p r : ℝ} (hr : 0 < r) (h : r < p) :
    0 < (p-r)*Real.log (p/r) :=
  mul_pos (sub_pos.mpr h) (Real.log_pos ((lt_div_iff₀ hr).2 (by simpa using h)))

section Tensor
variable {I : Type*} [Fintype I] [DecidableEq I]

def pushAxis (C : I → I → ℝ) (x : I → ℝ) (a : I) : ℝ := ∑ i, x i * C i a

theorem inverse_axis (C W : I → I → ℝ)
    (h : ∀ i j, ∑ a, C i a * W a j = if i = j then 1 else 0) (x : I → ℝ) :
    pushAxis W (pushAxis C x) = x := by
  funext j
  unfold pushAxis
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, h, mul_ite, mul_one, mul_zero]
  simp

def lift2 (C : I → I → ℝ) (p : I → I → ℝ) (a b : I) : ℝ :=
  pushAxis C (fun j => pushAxis C (fun i => p i j) a) b

def lift3 (C : I → I → ℝ) (p : I → I → I → ℝ) (a b c : I) : ℝ :=
  pushAxis C (fun k => lift2 C (fun i j => p i j k) a b) c

theorem inverse2 (C W : I → I → ℝ)
    (h : ∀ i j, ∑ a, C i a * W a j = if i = j then 1 else 0) (p : I → I → ℝ) :
    lift2 W (lift2 C p) = p := by
  have commute (i a : I) :
      pushAxis W (fun u => lift2 C p u a) i = pushAxis C (p i) a := by
    unfold lift2 pushAxis
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [show ∀ u j, (∑ v, p v j * C v u) * C j a * W u i =
      (∑ v, p v j * C v u) * W u i * C j a by intros; ring, ← Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (· * C j a)
      (congrFun (inverse_axis C W h (fun v => p v j)) i))
  funext i j
  change pushAxis W (fun v => pushAxis W (fun u => lift2 C p u v) i) j = _
  simp_rw [commute]
  exact congrFun (inverse_axis C W h (p i)) j

-- Scalar extraction with the same observed/reference orientation as Eq. (13).
theorem inverse3_weights (C W : I → I → ℝ)
    (h : ∀ i j, ∑ a, C i a * W a j = if i = j then 1 else 0)
    (p : I → I → I → ℝ) (i j k : I) :
    (∑ a, ∑ b, ∑ c, lift3 C p a b c * W c k * W b j * W a i) = p i j k := by
  have hlast (a b : I) :
      (∑ c, lift3 C p a b c * W c k) = lift2 C (fun u v => p u v k) a b :=
    congrFun (inverse_axis C W h (fun z => lift2 C (fun u v => p u v z) a b)) k
  simp only [← Finset.sum_mul, hlast]
  have hi := congrFun (congrFun (inverse2 C W h (fun u v => p u v k)) i) j
  apply Eq.trans _ hi
  change (∑ a, (∑ b, lift2 C (fun u v => p u v k) a b * W b j) * W a i) =
    ∑ b, (∑ a, lift2 C (fun u v => p u v k) a b * W a i) * W b j
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end Tensor

-- The eight binary words T_{000},...,T_{111}. Adjacent-position stationarity
-- forces equality of the only two nontrivial order-reversed pairs.
def boolSum (f : Bool → ℝ) := f false + f true

theorem binary_order_reversal (T : Bool → Bool → Bool → ℝ)
    (hs : ∀ i j, boolSum (T i j) = boolSum (fun k => T k i j)) (i j k : Bool) :
    T i j k = T k j i := by
  have h00 := hs false false
  have h11 := hs true true
  unfold boolSum at h00 h11
  cases i <;> cases j <;> cases k <;> linarith

def corr01 (T : Bool → Bool → Bool → ℝ) :=
  boolSum fun i => boolSum fun j => boolSum fun k => (if i=j then 1 else -1)*T i j k

def corr02 (T : Bool → Bool → Bool → ℝ) :=
  boolSum fun i => boolSum fun j => boolSum fun k => (if i=k then 1 else -1)*T i j k

def binaryMass (T : Bool → Bool → Bool → ℝ) :=
  boolSum fun i => boolSum fun j => boolSum fun k => T i j k

theorem binary_triple_identified (T U : Bool → Bool → Bool → ℝ)
    (ht : ∀ i j, boolSum (T i j) = boolSum (fun k => T k i j))
    (hu : ∀ i j, boolSum (U i j) = boolSum (fun k => U k i j))
    (ct : ∀ i j k, T (!i) (!j) (!k) = T i j k)
    (cu : ∀ i j k, U (!i) (!j) (!k) = U i j k)
    (hm : binaryMass T = binaryMass U) (h1 : corr01 T = corr01 U) (h2 : corr02 T = corr02 U) :
    T = U := by
  have t00 := ht false false
  have u00 := hu false false
  have t1 := ct false false false
  have t2 := ct false false true
  have t3 := ct false true false
  have t4 := ct false true true
  have u1 := cu false false false
  have u2 := cu false false true
  have u3 := cu false true false
  have u4 := cu false true true
  simp [boolSum,binaryMass,corr01,corr02] at *
  funext i j k
  cases i <;> cases j <;> cases k <;> linarith



def binaryStep : Bool → Bool → S
  | false,true => E | true,false => R | _,_ => P

def pushBinary (T : Bool → Bool → Bool → ℝ) : Pair :=
  fun x y => boolSum fun i => boolSum fun j => boolSum fun k =>
    if binaryStep i j = x ∧ binaryStep j k = y then T i j k else 0

theorem binary_pairs_symmetric (T : Bool → Bool → Bool → ℝ)
    (hs : ∀ i j, boolSum (T i j) = boolSum (fun k => T k i j)) :
    reversePair (pushBinary T) = pushBinary T := by
  have h0 := hs false false
  have h1 := hs true true
  simp [boolSum] at h0 h1
  funext i j
  cases i <;> cases j <;> simp [reversePair,flip,pushBinary,boolSum,binaryStep] <;> linarith

theorem binary_paths_witness (w : Bool → Bool → Bool → Bool → ℝ) :
    (boolSum fun i => boolSum fun j => boolSum fun k => boolSum fun l =>
      if binaryStep i j = P ∧ binaryStep j k = R ∧ binaryStep k l = E then w i j k l else 0) -
    (boolSum fun i => boolSum fun j => boolSum fun k => boolSum fun l =>
      if binaryStep i j = R ∧ binaryStep j k = E ∧ binaryStep k l = P then w i j k l else 0)
    = w true true false true - w true false true true := by
  simp [boolSum,binaryStep]

theorem marginal_even (J : Pair) (hs : stationary J) (ht : reversePair J = J) (i : S) :
    row J (flip i) = row J i := by
  have hc : row (reversePair J) i = col J (flip i) := by
    cases i <;> simp [row,col,reversePair,flip] <;> ring
  rw [ht, ← hs (flip i)] at hc
  exact hc.symm

def recoveredK (J : Pair) (i j : S) : ℝ :=
    if row J i = 0 then if i=j then 1 else 0 else J i j / row J i

theorem recovered_flux (J : Pair) (hn : ∀ i j, 0 ≤ J i j) (i j : S) :
    row J i * recoveredK J i j = J i j := by
  by_cases h : row J i = 0
  · have he := hn i E
    have hp := hn i P
    have hr := hn i R
    unfold row at h
    rw [recoveredK, show row J i = 0 by exact h, if_pos rfl, zero_mul]
    cases j <;> linarith
  · simp only [recoveredK, if_neg h]
    field_simp

theorem recovered_rows (J : Pair) (i : S) : row (recoveredK J) i = 1 := by
  by_cases h : row J i = 0
  · unfold row
    simp only [recoveredK,if_pos h]
    cases i <;> simp
  · unfold row
    simp only [recoveredK,if_neg h,← add_div]
    change row J i / row J i = 1
    exact div_self h

theorem markov_realization (J : Pair) (hs : stationary J) (ht : reversePair J = J)
    (hn : ∀ i j, 0 ≤ J i j) (a : S) (w : List S) :
    row J a * productPairs (recoveredK J) a w =
      row J (flip (endpoint a w)) * productPairs (recoveredK J)
        (flip (endpoint a w)) (reverseWord (a :: w)).tail := by
  refine reversal_flux (recoveredK J) (row J) ?_ (marginal_even J hs ht) a w
  intro i j
  rw [recovered_flux J hn i j,recovered_flux J hn (flip j) (flip i)]
  exact (congrFun (congrFun ht i) j).symm

def cycleSymbol (i : Fin 6) : S :=
  match i.val with
  | 0 | 3 => E
  | 1 | 5 => P
  | _ => R

def marker (i : Fin 6) : Bool :=
  match i.val with
  | 1 | 2 | 4 => true
  | _ => false

theorem cycle_reflect : ∀ i : Fin 6, cycleSymbol (-i) = cycleSymbol i := by decide

theorem rotor_reflect : ∀ i : Fin 6, marker (1-i) = !(marker i) := by decide

theorem rotor_steps :
    ∀ i : Fin 6, binaryStep (marker i) (marker (i+1)) = cycleSymbol i := by decide

theorem ctrl_emission_parity (η : ℝ) (i j : S) :
    em η (flip i) (flip j) = em η i j := by
  cases i <;> cases j <;> rfl

def ctrlTheta (x : Bool × Fin 6) : Bool × Fin 6 := (!x.1,-x.2)

def ctrlEmission (x : Bool × Fin 6) : S :=
  if x.1 then cycleSymbol x.2 else flip (cycleSymbol (-x.2))

theorem ctrl_reflect : ∀ x : Bool × Fin 6, ctrlEmission (ctrlTheta x) = flip (ctrlEmission x) := by
  decide

def ctrlAdvance (x : Bool × Fin 6) : Bool × Fin 6 := (x.1,x.2+1)

theorem ctrl_advance_reflect :
    ∀ x y : Bool × Fin 6, ctrlAdvance x = y ↔ ctrlAdvance (ctrlTheta y) = ctrlTheta x := by decide

theorem ctrl_kernel_reversal (ρ : ℝ) (i j : Bool × Fin 6) :
    ((if ctrlAdvance i = j then 1-ρ else 0) + ρ/12) =
      (if ctrlAdvance (ctrlTheta j) = ctrlTheta i then 1-ρ else 0) + ρ/12 := by
  by_cases h : ctrlAdvance i = j
  · simp [h, (ctrl_advance_reflect i j).mp h]
  · have hrev : ¬ctrlAdvance (ctrlTheta j) = ctrlTheta i :=
      fun hr => h ((ctrl_advance_reflect i j).mpr hr)
    simp [h,hrev]

theorem positive_emission {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (i j : S) :
    0 < em η i j := by
  unfold em
  split <;> linarith

theorem phase_recurrence_witness {η : ℝ} (hη : η < 1) :
    mean (fun i => em η i E * em η i E) - (mean (em η · E))^2 =
      (2/9)*(1-η)^2 ∧ 0 < (2/9 : ℝ)*(1-η)^2 := by
  constructor
  · simp [mean,em]
    ring
  · exact mul_pos (by norm_num) (pow_pos (by linarith) _)

def pauseErrors (η α β : ℝ) (i : S) : S → ℝ
  | E => (1-α)*em η i E
  | P => em η i P+α*em η i E+β*em η i R
  | R => (1-β)*em η i R

theorem pause_error_example :
    let e := (pauseErrors (1/4) (4/25) 0 · E)
    let p := (pauseErrors (1/4) (4/25) 0 · P)
    let r := (pauseErrors (1/4) (4/25) 0 · R)
    ctrl3 (1/5) p r e - ctrl3 (1/5) r e p = (4032 : ℝ)/1000000 := by
  norm_num [ctrl3,ctrl2,directed2,cyc3,cyc2,mean,pauseErrors,em,flip]

section FiniteKL

variable {I : Type*} [Fintype I]

noncomputable def blockKL (θ : I ≃ I) (p : I → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / p (θ x))

theorem blockKL_symmetrize (θ : I ≃ I) (p : I → ℝ)
    (hh : Function.Involutive θ) (hp : ∀ i, 0 < p i) :
    blockKL θ p = (∑ i, (p i - p (θ i)) * Real.log (p i/p (θ i)))/2 := by
  let f := fun x => p x * Real.log (p x/p (θ x))
  have hsum : (∑ x, f (θ x)) = ∑ x, f x := θ.sum_comp f
  have hpt (x : I) : f x + f (θ x) = (p x-p (θ x))*Real.log (p x/p (θ x)) := by
    simpa [f, hh x] using conjugate_kl_term (hp x) (hp (θ x))
  have hs : (∑ x, (f x + f (θ x))) =
      ∑ x, (p x-p (θ x))*Real.log (p x/p (θ x)) :=
    Finset.sum_congr rfl (fun x _ => hpt x)
  rw [Finset.sum_add_distrib, hsum] at hs
  unfold blockKL
  change (∑ x, f x) = _
  linarith

theorem blockKL_witness (θ : I ≃ I) (p : I → ℝ)
    (hh : Function.Involutive θ) (hp : ∀ i, 0 < p i)
    (i : I) (hi : p (θ i) < p i) :
    blockKL θ p ≥ (p i-p (θ i))*Real.log (p i/p (θ i)) ∧
    0 < (p i-p (θ i))*Real.log (p i/p (θ i)) := by
  classical
  let g := fun x => (p x-p (θ x))*Real.log (p x/p (θ x))
  have hnn (x : I) : 0 ≤ g x := pair_kl_nonneg (hp x) (hp (θ x))
  have hn : i ≠ θ i := by
    intro h
    exact (ne_of_gt hi) (congrArg p h)
  have hg : g (θ i) = g i := by
    dsimp [g]
    rw [hh i, Real.log_div (ne_of_gt (hp (θ i))) (ne_of_gt (hp i)),
      Real.log_div (ne_of_gt (hp i)) (ne_of_gt (hp (θ i)))]
    ring
  have hb : (∑ x ∈ ({i,θ i} : Finset I), g x) ≤ ∑ x, g x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hnn x)
  rw [Finset.sum_insert (by simp [hn]), Finset.sum_singleton, hg] at hb
  refine ⟨?_, pair_kl_positive (hp (θ i)) hi⟩
  rw [blockKL_symmetrize θ p hh hp]
  change (∑ x, g x) / 2 ≥ g i
  linarith

end FiniteKL

def rotorR (a u : ℝ) : ℝ :=
  (2/9*Real.exp (-u/2) + 2/3*Real.exp (-3*u/2)) *
    Real.cos (Real.sqrt 3*a*u/2) + (1/9)*Real.exp (-2*u)

def rotorGap (a : ℝ) : ℝ := rotorR a 2 - (rotorR a 1)^2

theorem rotorGap_continuous : Continuous rotorGap := by
  unfold rotorGap rotorR
  fun_prop

-- Analytic closure once the model-specific bounds on the gap and contrast hold.
theorem matched_witness {l h : ℝ} (hlh : l ≤ h) (δ : ℝ → ℝ)
    (hl : 0 ≤ rotorGap l) (hh : rotorGap h ≤ 0)
    (hd : ∀ a ∈ Set.Icc l h, δ a > 0) :
    ∃ a ∈ Set.Icc l h, rotorR a 2 = (rotorR a 1)^2 ∧ δ a > 0 := by
  obtain ⟨a,ha,hz⟩ := intermediate_value_Icc' hlh rotorGap_continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (rotorGap h) (rotorGap l) from ⟨hh,hl⟩)
  exact ⟨a,ha,sub_eq_zero.mp hz,hd a ha⟩

def markerCorr6Sum (d : Fin 6) : ℤ :=
  (([0,1,2,3,4,5] : List (Fin 6)).map
    (fun i => if marker i = marker (i+d) then (1 : ℤ) else -1)).sum

def harmonic1Twice (d : Fin 6) : ℤ :=
  match d.val with
  | 0 => 2 | 1 | 5 => 1 | 2 | 4 => -1 | _ => -2

def harmonic2Twice (d : Fin 6) : ℤ :=
  match d.val with
  | 0 | 3 => 2 | _ => -1

def harmonic3 (d : Fin 6) : ℤ := if d.val % 2 = 0 then 1 else -1

-- Exact discrete spectral weights, represented with integer coefficients.
theorem rotor_harmonics :
    ∀ d : Fin 6, 3 * markerCorr6Sum d =
      2*harmonic1Twice d+6*harmonic2Twice d+2*harmonic3 d := by
  decide

-- The two continuous-time damping rates and the alternating-mode rate.
theorem rotor_damping {p m : ℝ} (h : p+m=1) :
    (p+m)*(1/2)-1= -(1/2) ∧
    (p+m)*(-(1/2))-1= -(3/2) ∧
    (p+m)*(-1)-1= -2 := by
  rw [h]
  norm_num

theorem rotor_entropy_sign {p m : ℝ} (hp : 0 < p) (hm : 0 < m) (hn : p ≠ m) :
    0 < (p-m)*Real.log (p/m) := by
  rcases lt_or_gt_of_ne hn with h | h
  · rw [Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr h)
      (sub_neg.mpr (Real.strictMonoOn_log hp hm h))
  · exact pair_kl_positive hm h

def classify (ε x : ℝ) : S :=
  if ε < x then E else if x < -ε then R else P

theorem signed_increment_reverses {ε : ℝ} (he : 0 ≤ ε) (x y : ℝ) :
    classify ε (x-y) = flip (classify ε (y-x)) := by
  unfold classify
  by_cases h1 : ε < x-y
  · have h2 : y-x < -ε := by linarith
    have h3 : ¬ ε < y-x := by linarith
    simp [h1,h2,h3,flip]
  · by_cases h2 : x-y < -ε
    · have h3 : ε < y-x := by linarith
      simp [h1,h2,h3,flip]
    · have h3 : ¬ ε < y-x := by linarith
      have h4 : ¬ y-x < -ε := by linarith
      simp [h1,h2,h3,h4,flip]

def controlKernel (ρ : ℝ) (i j : Bool × Fin 6) : ℝ :=
  (if ctrlAdvance i = j then 1-ρ else 0) + ρ/12

theorem control_paths (ρ : ℝ) (i : Bool × Fin 6) (w : List (Bool × Fin 6)) :
    productPairs (controlKernel ρ) i w =
      productPairs (controlKernel ρ) (ctrlTheta (endpoint i w))
        (reverseMapped ctrlTheta (i :: w)).tail := by
  have h :=
    reversal_flux_general ctrlTheta (controlKernel ρ) (fun _ => (1 : ℝ))
      (fun a b => by simpa [controlKernel] using ctrl_kernel_reversal ρ a b)
      (fun _ => rfl) i w
  simpa using h

theorem finite_reset_retains_no_reset_weight (ρ : ℝ) (n : ℕ) :
    (1-ρ)^(n+1) = (1-ρ)^n*(1-ρ) := pow_succ _ _

theorem c0_exact :
    let a := (86/100 : ℚ)
    let b := (4/100 : ℚ)
    let c := (10/100 : ℚ)
    let d := (3/100 : ℚ)
    let e := (94/100 : ℚ)
    let f := (3/100 : ℚ)
    let g := (3/100 : ℚ)
    let h := (5/100 : ℚ)
    let i := (92/100 : ℚ)
    a+b+c=1 ∧ d+e+f=1 ∧ g+h+i=1 ∧
    0 < a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g) := by norm_num

def poissonWeight (u : ℝ) (n : ℕ) : ℝ := u^n / (n.factorial : ℝ)

theorem poisson_weight_succ (u : ℝ) (n : ℕ) :
    poissonWeight u (n+1) = poissonWeight u n * (u / (n+1)) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  simp only [poissonWeight,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

theorem poisson_term_bound {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    poissonWeight u (13+k) ≤ poissonWeight u 13 * (u/14)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ poissonWeight u (13+k) := by
      apply div_nonneg (pow_nonneg hu _)
      exact_mod_cast (Nat.zero_le (13+k).factorial)
    have hk : (14 : ℝ) ≤ (↑(13+k : ℕ) : ℝ)+1 := by
      push_cast
      have h : 0 ≤ (k : ℝ) := by positivity
      linarith
    rw [show 13+(k+1)=13+k+1 by omega,poisson_weight_succ,pow_succ,← mul_assoc]
    have ratio : u / ((↑(13+k : ℕ) : ℝ)+1) ≤ u/14 :=
      div_le_div_of_nonneg_left hu (by norm_num) hk
    exact (mul_le_mul_of_nonneg_left ratio hp).trans
      (mul_le_mul_of_nonneg_right ih (div_nonneg hu (by norm_num)))

theorem poisson_tail_bound {u : ℝ} (hu : 0 ≤ u) (hu' : u < 14) :
    (∑' k : ℕ, poissonWeight u (13+k)) ≤ poissonWeight u 13 / (1-u/14) := by
  have h0 : 0 ≤ u/14 := div_nonneg hu (by norm_num)
  have h1 : u/14 < 1 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 14)).mpr (by linarith)
  have hs := (summable_geometric_of_lt_one h0 h1).mul_left (poissonWeight u 13)
  have ht : Summable (fun k : ℕ => poissonWeight u (13+k)) :=
    Summable.of_nonneg_of_le
      (fun k => div_nonneg (pow_nonneg hu _) (by exact_mod_cast Nat.zero_le (13+k).factorial))
      (poisson_term_bound hu) hs
  calc
    _ ≤ ∑' k : ℕ, poissonWeight u 13 * (u/14)^k :=
      ht.tsum_le_tsum (poisson_term_bound hu) hs
    _ = _ := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one h0 h1]
      exact (div_eq_mul_inv (poissonWeight u 13) (1-u/14)).symm

theorem equilibrium_binary_lag_two (f : ℝ) :
    ((1-f)^2+f^2) - 2*f*(1-f) = (1-2*f)^2 := by ring

end
end IncrementCycles
