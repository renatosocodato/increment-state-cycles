import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Factorial.Basic

namespace RotorRational

structure Box where
  lo : ℚ
  hi : ℚ

def point (x : ℚ) : Box := ⟨x,x⟩
def plus (x y : Box) : Box := ⟨x.lo+y.lo,x.hi+y.hi⟩
def minus (x y : Box) : Box := ⟨x.lo-y.hi,x.hi-y.lo⟩
-- All arguments of this product are nonnegative in the kernel and word sums.
def times (x y : Box) : Box := ⟨x.lo*y.lo,x.hi*y.hi⟩
def scale (q : ℚ) (x : Box) : Box :=
  if q < 0 then ⟨q*x.hi,q*x.lo⟩ else ⟨q*x.lo,q*x.hi⟩

def sites : List (Fin 6) := [0,1,2,3,4,5]

def uniformized (u : Nat) (a : Box) : Fin 6 → Box :=
  let cw := scale (1/2) (plus (point 1) a)
  let ccw := scale (1/2) (minus (point 1) a)
  let initial : Array Box := (sites.map fun d => point (if d=0 then 1 else 0)).toArray
  let get := fun (xs : Array Box) (d : Fin 6) => xs[d.val]?.getD (point 0)
  let truncated := (List.range 12).foldl (fun acc k =>
    let n := k+1
    let weight : ℚ := (u : ℚ)^n / (Nat.factorial n : ℚ)
    let walk := (sites.map fun d =>
      plus (times (get acc.1 (d-1)) cw) (times (get acc.1 (d+1)) ccw)).toArray
    let sums := (sites.map fun d => plus (get acc.2.1 d) (scale weight (get walk d))).toArray
    (walk,sums,acc.2.2+weight)) (initial,initial,(1 : ℚ))
  let tail : ℚ := ((u : ℚ)^13 / (Nat.factorial 13 : ℚ)) / (1-(u : ℚ)/14)
  fun d =>
    let x := get truncated.2.1 d
    ⟨x.lo/(truncated.2.2+tail),(x.hi+tail)/truncated.2.2⟩

def correlation (k : Fin 6 → Box) : Box :=
  -- Exact signed autocorrelation at each deterministic displacement.
  let weights : List ℚ := [1,-1/3,-1/3,1/3,-1/3,-1/3]
  (sites.zip weights).foldl (fun acc (d,c) => plus acc (scale c (k d))) (point 0)

def gap (a : ℚ) : Box :=
  let r1 := correlation (uniformized 1 (point a))
  minus (correlation (uniformized 2 (point a))) (times r1 r1)

def lowSites : List (Fin 6) := [0,3,5]
def highSites : List (Fin 6) := [1,2,4]

def word (k : Fin 6 → Box) (b c d e : List (Fin 6)) : Box :=
  let terms := b.flatMap fun i => c.flatMap fun j => d.flatMap fun l => e.map fun m =>
    times (times (k (j-i)) (k (l-j))) (k (m-l))
  scale (1/6) (terms.foldl plus (point 0))

def low : ℚ := 52363/100000
def high : ℚ := 52365/100000
def intervalContrast : Box :=
  let ks := (sites.map (uniformized 1 ⟨low,high⟩)).toArray
  let k := fun d : Fin 6 => ks[d.val]?.getD (point 0)
  minus (word k highSites highSites lowSites highSites)
    (word k highSites lowSites highSites highSites)

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem lower_bracket_sign : 0 < (gap low).lo := by decide +kernel
theorem upper_bracket_sign : (gap high).hi < 0 := by decide +kernel
theorem positive_whole_bracket : (23/10000 : ℚ) < intervalContrast.lo := by decide +kernel

end RotorRational
