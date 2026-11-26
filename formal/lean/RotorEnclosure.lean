import IncrementCycles
import RotorRational
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.FunctionSeries

open scoped BigOperators
open IncrementCycles
open RotorRational

namespace RotorEnclosure

noncomputable section

def contains (b : Box) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

theorem point_contains (x : ℚ) : contains (point x) x := ⟨le_rfl,le_rfl⟩

theorem plus_contains {b c : Box} {x y : ℝ} (hx : contains b x) (hy : contains c y) :
    contains (plus b c) (x+y) := by
  unfold contains plus
  push_cast
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem minus_contains {b c : Box} {x y : ℝ} (hx : contains b x) (hy : contains c y) :
    contains (minus b c) (x-y) := by
  unfold contains minus
  push_cast
  exact ⟨sub_le_sub hx.1 hy.2,sub_le_sub hx.2 hy.1⟩

theorem times_contains {b c : Box} {x y : ℝ} (hx : contains b x) (hy : contains c y)
    (hb : 0 ≤ b.lo) (hc : 0 ≤ c.lo) : contains (times b c) (x*y) := by
  have hbr : (0 : ℝ) ≤ (b.lo : ℝ) := by exact_mod_cast hb
  have hcr : (0 : ℝ) ≤ (c.lo : ℝ) := by exact_mod_cast hc
  unfold contains times
  push_cast
  exact ⟨mul_le_mul hx.1 hy.1 hcr (hbr.trans hx.1),
    mul_le_mul hx.2 hy.2 (hcr.trans hy.1) ((hbr.trans hx.1).trans hx.2)⟩

theorem scale_contains (q : ℚ) {b : Box} {x : ℝ} (hx : contains b x) :
    contains (scale q b) ((q : ℝ)*x) := by
  by_cases hq : q < 0
  · have hr : (q : ℝ) ≤ 0 := by exact_mod_cast hq.le
    simp only [contains,scale,if_pos hq,Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hr,mul_le_mul_of_nonpos_left hx.1 hr⟩
  · have hr : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_not_gt hq
    simp only [contains,scale,if_neg hq,Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hr,mul_le_mul_of_nonneg_left hx.2 hr⟩

def cw (a : Box) := scale (1/2) (plus (point 1) a)
def ccw (a : Box) := scale (1/2) (minus (point 1) a)
def forward (a : ℝ) := (1+a)/2
def backward (a : ℝ) := (1-a)/2

theorem cw_contains {a : Box} {x : ℝ} (hx : contains a x) : contains (cw a) (forward x) := by
  unfold cw
  convert scale_contains (1/2) (plus_contains (point_contains 1) hx) using 1
  norm_num [forward]
  ring

theorem ccw_contains {a : Box} {x : ℝ} (hx : contains a x) : contains (ccw a) (backward x) := by
  unfold ccw
  convert scale_contains (1/2) (minus_contains (point_contains 1) hx) using 1
  norm_num [backward]
  ring

def validBias (a : Box) : Prop := -1 ≤ a.lo ∧ a.hi ≤ 1

theorem bias_nonneg {a : Box} (ha : validBias a) : 0 ≤ (cw a).lo ∧ 0 ≤ (ccw a).lo := by
  have h₁ := ha.1
  have h₂ := ha.2
  norm_num [cw,ccw,scale,plus,minus,point]
  constructor <;> linarith

def atV (xs : Vector Box 6) (d : Fin 6) : Box := xs[d.val]

def walkB (a : Box) : ℕ → Vector Box 6
  | 0 => Vector.ofFn fun d => point (if d=0 then 1 else 0)
  | n+1 =>
    let w := walkB a n
    Vector.ofFn fun d => plus (times (atV w (d-1)) (cw a))
      (times (atV w (d+1)) (ccw a))

def walk (a : ℝ) : ℕ → Fin 6 → ℝ
  | 0, d => if d=0 then 1 else 0
  | n+1, d => walk a n (d-1) * forward a + walk a n (d+1) * backward a

theorem walk_nonneg_le_one {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) (n : ℕ) (d : Fin 6) :
    0 ≤ walk x n d ∧ walk x n d ≤ 1 := by
  have hF : 0 ≤ forward x := by unfold forward; linarith [hx.1]
  have hB : 0 ≤ backward x := by unfold backward; linarith [hx.2]
  induction n generalizing d with
  | zero => simp [walk]; split <;> norm_num
  | succ n ih =>
    simp only [walk]
    have hl := ih (d-1)
    have hr := ih (d+1)
    constructor
    · exact add_nonneg (mul_nonneg hl.1 hF) (mul_nonneg hr.1 hB)
    · calc
        _ ≤ 1*forward x + 1*backward x :=
          add_le_add (mul_le_mul_of_nonneg_right hl.2 hF) (mul_le_mul_of_nonneg_right hr.2 hB)
        _ = 1 := by unfold forward backward; ring

theorem walk_enclosure {a : Box} {x : ℝ} (ha : validBias a) (hx : contains a x)
    (n : ℕ) (d : Fin 6) : contains (atV (walkB a n) d) (walk x n d) ∧
      0 ≤ (atV (walkB a n) d).lo := by
  induction n generalizing d with
  | zero =>
    simp only [walkB,atV,Vector.getElem_ofFn,Fin.eta,walk]
    by_cases h : d=0 <;> simp [h,contains,point]
  | succ n ih =>
    have l := ih (d-1)
    have r := ih (d+1)
    have h := bias_nonneg ha
    simp only [walkB,atV,Vector.getElem_ofFn,Fin.eta,walk]
    exact ⟨plus_contains
          (times_contains l.1 (cw_contains hx) l.2 h.1)
          (times_contains r.1 (ccw_contains hx) r.2 h.2),
        add_nonneg (mul_nonneg l.2 h.1) (mul_nonneg r.2 h.2)⟩

def qWeight (u n : ℕ) : ℚ := (u : ℚ)^n / (n.factorial : ℚ)

theorem qWeight_cast (u n : ℕ) : (qWeight u n : ℝ) = poissonWeight u n := by
  simp [qWeight,poissonWeight]

def partialB (u : ℕ) (a : Box) : ℕ → Vector Box 6
  | 0 => walkB a 0
  | n+1 =>
    let w := walkB a (n+1)
    let prev := partialB u a n
    Vector.ofFn fun d => plus (atV prev d) (scale (qWeight u (n+1)) (atV w d))

theorem partial_enclosure (u n : ℕ) {a : Box} {x : ℝ} (ha : validBias a) (hx : contains a x)
    (d : Fin 6) : contains (atV (partialB u a n) d)
      (∑ i ∈ Finset.range (n+1), poissonWeight u i * walk x i d) ∧
      0 ≤ (atV (partialB u a n) d).lo := by
  induction n with
  | zero =>
    simpa [partialB,poissonWeight] using walk_enclosure ha hx 0 d
  | succ n ih =>
    have w := walk_enclosure ha hx (n+1) d
    have hq : (0 : ℚ) ≤ qWeight u (n+1) := by unfold qWeight; positivity
    rw [show n+1+1=n+2 by omega, Finset.sum_range_succ]
    simp only [partialB,atV,Vector.getElem_ofFn]
    refine ⟨plus_contains ih.1 ?_,?_⟩
    · rw [← qWeight_cast]
      exact scale_contains _ w.1
    · simp [plus,scale,not_lt.mpr hq]
      exact add_nonneg ih.2 (mul_nonneg hq w.2)

def normalB (u : ℕ) : ℕ → ℚ
  | 0 => 1
  | n+1 => normalB u n + qWeight u (n+1)

def tailB (u : ℕ) : ℚ := qWeight u 13 / (1-(u : ℚ)/14)

def enclosedKernel (u : ℕ) (a : Box) (d : Fin 6) : Box :=
  let b := atV (partialB u a 12) d
  ⟨b.lo/(normalB u 12 + tailB u),(b.hi+tailB u)/normalB u 12⟩

def kernel (u a : ℝ) (d : Fin 6) : ℝ :=
  (∑' n, poissonWeight u n * walk a n d) / Real.exp u

theorem poisson_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ poissonWeight u n := by
  unfold poissonWeight
  positivity

theorem poisson_summable (u : ℝ) : Summable (poissonWeight u) :=
  NormedSpace.expSeries_div_summable u

theorem poisson_total (u : ℝ) : (∑' n, poissonWeight u n) = Real.exp u := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rfl

theorem kernel_series_summable {a u : ℝ} (hu : 0 ≤ u) (ha : -1 ≤ a ∧ a ≤ 1) (d : Fin 6) :
    Summable (fun n => poissonWeight u n * walk a n d) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poisson_nonneg hu n) (walk_nonneg_le_one ha n d).1)
    (fun n => mul_le_of_le_one_right (poisson_nonneg hu n) (walk_nonneg_le_one ha n d).2)
    (poisson_summable u)

theorem kernel_continuous (u : ℝ) (hu : 0 ≤ u) (d : Fin 6) :
    ContinuousOn (fun a => kernel u a d) (Set.Icc (-1 : ℝ) 1) := by
  have hw (n : ℕ) (d : Fin 6) : Continuous (fun a => walk a n d) := by
    induction n generalizing d with
    | zero => simpa only [walk] using continuous_const
    | succ n ih =>
      simp only [walk]
      exact ((ih (d-1)).mul (by unfold forward; fun_prop)).add
        ((ih (d+1)).mul (by unfold backward; fun_prop))
  unfold kernel
  apply ContinuousOn.div_const
  apply continuousOn_tsum (u:=poissonWeight u)
  · intro n
    exact (continuous_const.mul (hw n d)).continuousOn
  · exact poisson_summable u
  · intro n a ha
    have hp := poisson_nonneg hu n
    have w := walk_nonneg_le_one ha n d
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp w.1)]
    exact mul_le_of_le_one_right hp w.2

theorem normalB_cast (u n : ℕ) :
    (normalB u n : ℝ) = ∑ i ∈ Finset.range (n+1), poissonWeight u i := by
  induction n with
  | zero => simp [normalB,poissonWeight]
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,Finset.sum_range_succ]
    simp only [normalB,Rat.cast_add,ih,qWeight_cast]

theorem tailB_cast (u : ℕ) :
    (tailB u : ℝ) = poissonWeight u 13 / (1-(u : ℝ)/14) := by
  unfold tailB
  push_cast
  rw [qWeight_cast]

theorem enclosedKernel_valid (u : ℕ) (hu : u < 14)
    {a : Box} {x : ℝ} (ha : validBias a) (hx : contains a x) (d : Fin 6) :
    contains (enclosedKernel u a d) (kernel u x d) ∧ 0 ≤ (enclosedKernel u a d).lo := by
  have u0 : 0 ≤ (u : ℝ) := by positivity
  have u14 : (u : ℝ) < 14 := by exact_mod_cast hu
  have hxl : (-1 : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast ha.1
  have hxr : (a.hi : ℝ) ≤ 1 := by exact_mod_cast ha.2
  have xok : -1 ≤ x ∧ x ≤ 1 := ⟨hxl.trans hx.1,hx.2.trans hxr⟩
  have ep := partial_enclosure u 12 ha hx d
  have eps := poisson_tail_bound u0 u14
  have nnk : ∀ n, 0 ≤ poissonWeight u n * walk x n d :=
    fun n => mul_nonneg (poisson_nonneg u0 n) (walk_nonneg_le_one xok n d).1
  have hle : ∀ n, poissonWeight u n * walk x n d ≤ poissonWeight u n :=
    fun n => mul_le_of_le_one_right (poisson_nonneg u0 n) (walk_nonneg_le_one xok n d).2
  have sk := kernel_series_summable u0 xok d
  have sp := poisson_summable u
  have sk' := (summable_nat_add_iff 13).mpr sk
  have sp' := (summable_nat_add_iff 13).mpr sp
  have hk0 : 0 ≤ ∑' n : ℕ, poissonWeight u (n+13) * walk x (n+13) d := tsum_nonneg (fun n => nnk _)
  have hp0 : 0 ≤ ∑' n : ℕ, poissonWeight u (n+13) := tsum_nonneg (fun n => poisson_nonneg u0 _)
  have hp1 : (∑' n : ℕ, poissonWeight u (n+13)) ≤ (tailB u : ℝ) := by
    rw [tailB_cast]
    simpa [Nat.add_comm] using eps
  have hk1 : (∑' n : ℕ, poissonWeight u (n+13) * walk x (n+13) d) ≤ (tailB u : ℝ) :=
    (sk'.tsum_le_tsum (fun n => hle _) sp').trans hp1
  have hn := sp.sum_add_tsum_nat_add 13
  rw [poisson_total, ← normalB_cast] at hn
  have hnum := sk.sum_add_tsum_nat_add 13
  have hlo : ((atV (partialB u a 12) d).lo : ℝ) ≤ ∑' n, poissonWeight u n * walk x n d := by
    linarith [ep.1.1]
  have hhi : (∑' n, poissonWeight u n * walk x n d) ≤
      ((atV (partialB u a 12) d).hi : ℝ) + (tailB u : ℝ) := by
    linarith [ep.1.2]
  have hun : 0 < (normalB u 12 : ℝ) := by
    rw [normalB_cast, Finset.sum_range_succ']
    simp only [poissonWeight, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun n _ => poisson_nonneg u0 (n+1))) zero_lt_one
  have hN1 : (normalB u 12 : ℝ) ≤ Real.exp u := by linarith
  have hN2 : Real.exp u ≤ (normalB u 12 : ℝ)+(tailB u : ℝ) := by linarith
  have hnl : 0 ≤ ((atV (partialB u a 12) d).lo : ℝ) := by exact_mod_cast ep.2
  have hnhi : 0 ≤ ((atV (partialB u a 12) d).hi : ℝ) + (tailB u : ℝ) :=
    (hnl.trans hlo).trans hhi
  have hv : 0 < (normalB u 12 : ℝ)+(tailB u : ℝ) := (Real.exp_pos u).trans_le hN2
  refine ⟨?_,?_⟩
  · unfold contains enclosedKernel kernel
    push_cast
    exact ⟨(div_le_div_of_nonneg_left hnl (Real.exp_pos u) hN2).trans
        (div_le_div_of_nonneg_right hlo (Real.exp_pos u).le),
      (div_le_div_of_nonneg_right hhi (Real.exp_pos u).le).trans
        (div_le_div_of_nonneg_left hnhi hun hN1)⟩
  · unfold enclosedKernel
    exact_mod_cast (div_nonneg hnl hv.le)

def listBox {A : Type*} (xs : List A) (b : A → Box) : Box :=
  (xs.map b).foldr plus (point 0)

def listVal {A : Type*} (xs : List A) (f : A → ℝ) : ℝ :=
  (xs.map f).sum

theorem list_contains {A : Type*} (xs : List A) (b : A → Box) (f : A → ℝ)
    (h : ∀ i ∈ xs, contains (b i) (f i)) : contains (listBox xs b) (listVal xs f) := by
  induction xs with
  | nil => simp [listBox,listVal,contains,point]
  | cons i xs ih =>
    exact plus_contains (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem listBox_nonneg {A : Type*} (xs : List A) (b : A → Box)
    (h : ∀ i ∈ xs, 0 ≤ (b i).lo) : 0 ≤ (listBox xs b).lo := by
  induction xs with
  | nil => norm_num [listBox,point]
  | cons i xs ih =>
    exact add_nonneg (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem listVal_continuousOn {A : Type*} (xs : List A) (f : A → ℝ → ℝ)
    {s : Set ℝ} (h : ∀ i ∈ xs, ContinuousOn (f i) s) :
    ContinuousOn (fun a => listVal xs (fun i => f i a)) s := by
  induction xs with
  | nil => exact continuousOn_const
  | cons i xs ih => exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

def rWeight (d : Fin 6) : ℚ :=
  match d.val with
  | 0 => 1 | 3 => 1/3 | _ => -1/3

theorem rWeight_marker (d : Fin 6) :
    (rWeight d : ℝ) = (markerCorr6Sum d : ℝ)/6 := by
  have h : ∀ i : Fin 6, rWeight i = (markerCorr6Sum i : ℚ)/6 := by decide +kernel
  exact_mod_cast h d

def corrB (k : Fin 6 → Box) : Box :=
  listBox sites (fun d => scale (rWeight d) (k d))

def corr (k : Fin 6 → ℝ) : ℝ :=
  listVal sites (fun d => (rWeight d : ℝ)*k d)

theorem corr_contains {b : Fin 6 → Box} {k : Fin 6 → ℝ}
    (h : ∀ d, contains (b d) (k d)) : contains (corrB b) (corr k) :=
  list_contains sites _ _ (fun d _ => scale_contains _ (h d))

def convB (b : Fin 6 → Box) (d : Fin 6) : Box :=
  listBox sites (fun j => times (b j) (b (d-j)))

def conv (k : Fin 6 → ℝ) (d : Fin 6) : ℝ :=
  listVal sites (fun j => k j * k (d-j))

theorem conv_contains {b : Fin 6 → Box} {k : Fin 6 → ℝ}
    (h : ∀ d, contains (b d) (k d) ∧ 0 ≤ (b d).lo) (d : Fin 6) :
    contains (convB b d) (conv k d) :=
  list_contains sites _ _ (fun j _ => times_contains (h j).1 (h (d-j)).1 (h j).2 (h (d-j)).2)

def liveCorr (a : ℝ) : ℝ := corr (kernel 1 a)
def liveGap (a : ℝ) : ℝ := corr (conv (kernel 1 a)) - liveCorr a ^ 2

def corrBox (a : Box) : Box := corrB (enclosedKernel 1 a)

def gapBox (a : Box) : Box :=
  let b := enclosedKernel 1 a
  let t := corrB b
  minus (corrB (convB b)) (times t t)

theorem liveGap_contains {b : Box} {x : ℝ} (ha : validBias b) (hx : contains b x)
    (hc : 0 ≤ (corrBox b).lo) : contains (gapBox b) (liveGap x) := by
  have h := enclosedKernel_valid 1 (by decide) ha hx
  have ht := corr_contains (fun d => (h d).1)
  simpa only [liveGap,liveCorr,gapBox,corrBox,pow_two,Nat.cast_one] using
    minus_contains (corr_contains (conv_contains h)) (times_contains ht ht hc hc)

theorem liveGap_continuous : ContinuousOn liveGap (Set.Icc (-1 : ℝ) 1) := by
  have hk (d : Fin 6) := kernel_continuous 1 (by norm_num) d
  have hcv (d : Fin 6) :
      ContinuousOn (fun a => conv (kernel 1 a) d) (Set.Icc (-1 : ℝ) 1) :=
    listVal_continuousOn sites _ (fun j _ => (hk j).mul (hk (d-j)))
  have hc (K : ℝ → Fin 6 → ℝ)
      (hK : ∀ d, ContinuousOn (fun a => K a d) (Set.Icc (-1 : ℝ) 1)) :
      ContinuousOn (fun a => corr (K a)) (Set.Icc (-1 : ℝ) 1) :=
    listVal_continuousOn sites _ (fun d _ => continuousOn_const.mul (hK d))
  exact (hc (fun a => conv (kernel 1 a)) hcv).sub ((hc (kernel 1) hk).pow 2)

def wordBox (b : Fin 6 → Box) (xs ys zs ws : List (Fin 6)) : Box :=
  scale (1/6) (listBox xs fun i => listBox ys fun j => listBox zs fun l => listBox ws fun m =>
    times (times (b (j-i)) (b (l-j))) (b (m-l)))

def observedWord (k : Fin 6 → ℝ) (xs ys zs ws : List (Fin 6)) : ℝ :=
  (1/6)*listVal xs fun i => listVal ys fun j => listVal zs fun l => listVal ws fun m =>
    k (j-i) * k (l-j) * k (m-l)

theorem word_contains {b : Fin 6 → Box} {k : Fin 6 → ℝ} (h : ∀ d, contains (b d) (k d) ∧ 0 ≤ (b d).lo)
    (xs ys zs ws : List (Fin 6)) : contains (wordBox b xs ys zs ws) (observedWord k xs ys zs ws) := by
  have v (i j l m : Fin 6) :=
    times_contains (times_contains (h (j-i)).1 (h (l-j)).1 (h (j-i)).2 (h (l-j)).2)
      (h (m-l)).1 (mul_nonneg (h (j-i)).2 (h (l-j)).2) (h (m-l)).2
  have hw := list_contains xs _ _ (fun i _ => list_contains ys _ _ (fun j _ =>
    list_contains zs _ _ (fun l _ => list_contains ws _ _ (fun m _ => v i j l m))))
  simpa [wordBox,observedWord] using scale_contains (1/6) hw

def liveContrast (a : ℝ) : ℝ :=
  let k := kernel 1 a
  observedWord k highSites highSites lowSites highSites - observedWord k highSites lowSites highSites highSites

def contrastBox (a : Box) : Box :=
  let b := enclosedKernel 1 a
  minus (wordBox b highSites highSites lowSites highSites) (wordBox b highSites lowSites highSites highSites)

theorem contrast_contains {b : Box} {a : ℝ} (hb : validBias b) (ha : contains b a) :
    contains (contrastBox b) (liveContrast a) :=
  by
    have h := enclosedKernel_valid 1 (by decide) hb ha
    have h'' : ∀ d, contains (enclosedKernel 1 b d) (kernel 1 a d) ∧
        0 ≤ (enclosedKernel 1 b d).lo := by simpa only [Nat.cast_one] using h
    exact minus_contains (word_contains h'' _ _ _ _) (word_contains h'' _ _ _ _)

def rootBox : Box := ⟨low,high⟩

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem root_domain : validBias rootBox := by unfold validBias; decide +kernel

theorem endpoint_signs_rational :
    0 < (gapBox (point low)).lo ∧ (gapBox (point high)).hi < 0 ∧
    0 ≤ (corrBox (point low)).lo ∧ 0 ≤ (corrBox (point high)).lo := by decide +kernel

theorem root_range_rational :
    (2436/1000000 : ℚ) < (contrastBox rootBox).lo ∧
    0 < (corrBox rootBox).lo ∧ (corrBox rootBox).hi < 1 := by decide +kernel

theorem rotor_matched_positive :
    ∃ a ∈ Set.Icc (low : ℝ) (high : ℝ),
      liveGap a = 0 ∧ (2436/1000000 : ℝ) < liveContrast a ∧ 0 < liveCorr a ∧ liveCorr a < 1 := by
  have h0 : validBias (point low) := by unfold validBias; decide +kernel
  have h1 : validBias (point high) := by unfold validBias; decide +kernel
  have hs := endpoint_signs_rational
  have hb : (low : ℝ) ≤ (high : ℝ) := by norm_num [low,high]
  have l := liveGap_contains h0 (point_contains low) hs.2.2.1
  have h := liveGap_contains h1 (point_contains high) hs.2.2.2
  have sl : 0 < (gapBox (point low)).lo := hs.1
  have sh : (gapBox (point high)).hi < 0 := hs.2.1
  have l' : 0 ≤ liveGap low := (show (0 : ℝ) < ((gapBox (point low)).lo : ℝ) by exact_mod_cast sl).le.trans l.1
  have h' : liveGap high ≤ 0 := h.2.trans (show ((gapBox (point high)).hi : ℝ) < 0 by exact_mod_cast sh).le
  have hj : Set.Icc (low : ℝ) (high : ℝ) ⊆ Set.Icc (-1 : ℝ) 1 :=
    Set.Icc_subset_Icc (by norm_num [low]) (by norm_num [high])
  obtain ⟨a,ha,hz⟩ := intermediate_value_Icc' hb (liveGap_continuous.mono hj)
    (show (0 : ℝ) ∈ Set.Icc (liveGap high) (liveGap low) from ⟨h',l'⟩)
  have hc := contrast_contains root_domain ha
  have hr : contains (corrBox rootBox) (liveCorr a) := by
    simpa only [corrBox,liveCorr,Nat.cast_one] using
      corr_contains (fun d => (enclosedKernel_valid 1 (by decide) root_domain ha d).1)
  have hRat := root_range_rational
  refine ⟨a,ha,hz,?_,?_,?_⟩
  · exact (show (2436/1000000 : ℝ) < ((contrastBox rootBox).lo : ℝ) by
      have hcast : ((2436/1000000 : ℚ) : ℝ) < ((contrastBox rootBox).lo : ℝ) := by exact_mod_cast hRat.1
      norm_num at hcast ⊢
      exact hcast).trans_le hc.1
  · exact (show (0 : ℝ) < ((corrBox rootBox).lo : ℝ) by exact_mod_cast hRat.2.1).trans_le hr.1
  · exact hr.2.trans_lt (show ((corrBox rootBox).hi : ℝ) < 1 by exact_mod_cast hRat.2.2)

end
end RotorEnclosure
